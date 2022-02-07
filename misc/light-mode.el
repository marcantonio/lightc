(defvar light-mode-hook nil)

(defun light-runner ()
  "Run Light JIT"
  (interactive)
  (start-process "light-runner"
                 (get-buffer-create "*light-buffer*")
                 "~/Code/lightc/target/debug/lightc"
                 "-j"
                 (buffer-file-name))
  (display-buffer "*light-buffer*"))

(defvar light-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\C-c\C-c\C-r" 'light-runner)
    map)
  "Keymap for Light major mode")

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.lt\\'" . light-mode))

;(regexp-opt '("extern" "else" "if" "for" "let" "fn"))
(defconst light-font-lock-keywords
  (list
   '("\\<\\(?:e\\(?:lse\\|xtern\\)\\|f\\(?:n\\|or\\)\\|if\\|let\\)\\>" . font-lock-keyword-face)
   '("//.*" . font-lock-comment-face)
   '("\".*\"" . font-lock-string-face)))

(defun light-indent-line ()
  "Indent current line as Light code"
  (interactive)
  (let ((pos (- (point-max) (point))))
    (beginning-of-line)
    (if (bobp)
        (indent-line-to 0)
      (let ((not-indented t) indent)
        (if (or (looking-at "^[ \t]*}[ \t]*\\(?://\\)?.*$")
                (looking-at "^[ \t]*}[ \t]*else[ \t]*{[ \t]*\\(?://\\)?.*$"))
            (progn
              (save-excursion
                (forward-line -1)
                (setq indent (- (current-indentation) tab-width)))
              (if (< indent 0)
                  (setq indent 0)))
          (save-excursion
            (while not-indented
              (forward-line -1)
              (cond ((looking-at ".*{[ \t]*\\(?://\\)?.*$")
                     (progn
                       (setq indent (+ (current-indentation) tab-width))
                       (setq not-indented nil)))
                    ((looking-at "^[ \t]*}")
                     (progn
                       (setq indent (current-indentation))
                       (setq not-indented nil)))
                    ((bobp)
                     (setq not-indented nil))))))
        (when indent
          (indent-line-to indent)
          (if (> (- (point-max) pos) (point))
	      (goto-char (- (point-max) pos))))))))

(defvar light-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?_ "w" st)
    (modify-syntax-entry ?/ ". 124b" st)
    (modify-syntax-entry ?* ". 23" st)
    (modify-syntax-entry ?\n "> b" st)
    st)
  "Syntax table for light-mode")

(defvar light-mode-tab-width 4 "Tab width in Light mode")

(define-derived-mode light-mode prog-mode "Light"
  "Major mode for Light code"
  :syntax-table light-mode-syntax-table
  (set (make-local-variable 'font-lock-defaults) '(light-font-lock-keywords))
  (set (make-local-variable 'indent-line-function) 'light-indent-line)
  (when light-mode-tab-width
    (setq tab-width light-mode-tab-width)))

(provide 'light-mode)
