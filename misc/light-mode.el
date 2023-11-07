;; Major mode for the Light programming language
;; Resources:
;;   - https://www.emacswiki.org/emacs/ModeTutorial
;;   - https://www.omarpolo.com/post/writing-a-major-mode.html
;;   - https://www.gnu.org/software/emacs/manual/html_node/elisp/index.html
;;   - https://github.com/dominikh/go-mode.el
;;   - https://github.com/rust-lang/rust-mode

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

(defconst light-keywords
  '("extern"
    "else"
    "if"
    "for"
    "let"
    "fn"
    "struct"
    "self"
    "true"
    "false"
    "module"
    "use"
    "loop"
    "break"
    "next"))

(defconst light-builtin-type
  '("int" "uint"
    "int8" "uint8"
    "int16" "uint16"
    "int32" "uint32"
    "int64" "uint64"
    "float" "double"
    "bool" "char"))

;; Matches fn `foo'()
(defconst light-fn-name-re "\\(?:fn\\|extern[[:space:]]fn\\)[[:space:]]+\\([[:word:]]+\\)")

;; Matches fn foo() -> `int'
(defconst light-fn-return-re "\\(?:fn\\|extern\\)[[:space:]]+[[:word:]]+.+->[[:space:]]+\\([[:word:]]+\\)")

;; Matches struct `foo'
(defconst light-struct-def-re "struct[[:space:]]+\\([[:word:]]+\\)")

;; Matches a `int' or [`int; 3']
(defconst light-type-re "\\[?\\([[:word:]]+\\)\\(?:[[:space:]]*;[[:space:]]+[[:digit:]]+\\]\\)?")

;; Matches `foo': int
(defconst light-typed-decl-re (concat "\\([[:word:]]+\\)[[:space:]]*:[[:space:]]+" light-type-re))

;; Matches module `foo'
(defconst light-mod-name-re "\\(?:module\\|use\\)[[:space:]]+\\([[:word:]]+\\)")

;; Matches `foo'::bar()
;; Not sure if I like this one...
(defconst light-mod-path-re "\\([[:word:]]+\\)::")

;; Identifies a closer. Used to skip further indentation when a block is closing
(defconst light-closing-brace-re "^[[:space:]]*[})].*$")

(defconst light-font-lock-keywords
  (append
   `(
     (,light-fn-name-re . (1 'font-lock-function-name-face))
     (,light-fn-return-re . (1 'font-lock-type-face))
     (,light-struct-def-re . (1 'font-lock-type-face))
     (,light-typed-decl-re . ((1 'font-lock-variable-name-face)
                              (2 'font-lock-type-face)))
     (,light-mod-name-re . (1 'font-lock-preprocessor-face))
     (,light-mod-path-re . (1 'font-lock-preprocessor-face))
     (,(regexp-opt light-builtin-type 'symbols) . font-lock-type-face)
     (,(regexp-opt light-keywords 'symbols) . font-lock-keyword-face))))

;; Helper to pull out the current index level
(defun light-indent-level ()
  (car (syntax-ppss)))

;; Find the indent level of the last opening paren/brace/etc. It works by jumping to the
;; beginning of the line (this lets us ignore other parens on the line), jumping back to
;; the last opener, then returning the current indent level
(defun light-find-enclosing-ident ()
  (let ((searching t))
    (save-excursion
      (beginning-of-line)
      (let ((opener-pos (nth 1 (syntax-ppss))))
        (when opener-pos
          (goto-char opener-pos)))
      (light-indent-level))))

(defun light-indent-line ()
  "Indent current line"
  (interactive)
  (let ((pos (- (point-max) (point))) ; used to follow the text if it moves
        (enclosing-indent (light-find-enclosing-ident)) ; ident of the last seen opener
        (ident 0))
    (beginning-of-line)
    ;; If the enclosing indent and the current indent match, we are at the top level and
    ;; shouldn't increase. This prevents openers from indenting
    (if (or (= enclosing-indent (light-indent-level))
            (looking-at light-closing-brace-re))
        (setq indent (* enclosing-indent tab-width))
      (setq indent (+ (* enclosing-indent tab-width) tab-width)))

    (indent-line-to indent)

    ;; If the cursor was in the indent space before any chars, do nothing (will jump to the
    ;; first char because of `indent-line-to`). Otherwise, jump to maintain the current
    ;; distance (pos) from the end of the buffer
    (if (> (- (point-max) pos) (point))
        (goto-char (- (point-max) pos)))))

(defvar light-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?_ "w" st)
    (modify-syntax-entry ?/ ". 124b" st)
    (modify-syntax-entry ?* ". 23" st)
    (modify-syntax-entry ?\n "> b" st)
    (modify-syntax-entry ?\" "\"" st)
    (modify-syntax-entry ?\' "\"" st)
    st)
  "Syntax table for light-mode")

(defvar light-mode-tab-width 4 "Tab width in Light mode")

(define-derived-mode light-mode prog-mode "Light"
  "Major mode for the Light programming language"
  :syntax-table light-mode-syntax-table
  (set (make-local-variable 'font-lock-defaults) '(light-font-lock-keywords))
  (set (make-local-variable 'indent-line-function) 'light-indent-line)
  (set (make-local-variable 'comment-start) "// ")
  (set (make-local-variable 'comment-start-skip) "//[[:space:]]*")
  (when light-mode-tab-width
    (setq tab-width light-mode-tab-width)))

(provide 'light-mode)
