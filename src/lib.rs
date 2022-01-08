use std::fmt::Display;

/// lexer ///
#[derive(Debug, PartialEq)]
pub enum Token {
    Fn,
    Let,
    OpenParen,
    CloseParen,
    OpenBrace,
    CloseBrace,
    Comma,
    Colon,
    Assign,
    Ident(String),
    Int(f64),
    VarType(Type),
    Op(char),
    GreaterThan,
    LessThan,
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug, PartialEq)]
pub enum Type {
    F64,
}

#[derive(Debug, PartialEq)]
pub enum LexError {
    InvalidNum,
}

pub type LexResult = std::result::Result<Vec<Token>, LexError>;

pub fn lexer(input: &str) -> LexResult {
    let mut tokens = vec![];

    // Main loop; one char at a time
    let mut stream: Vec<char> = input.chars().rev().collect();
    'main: while let Some(cur) = stream.pop() {
        // Ignore whitespace
        if cur.is_ascii_whitespace() {
            while let Some(c) = stream.pop() {
                if !c.is_ascii_whitespace() {
                    stream.push(c);
                    break;
                }
            }
        }

        // Comments
        if cur == '/' && stream.last() == Some(&'/') {
            while let Some(c) = stream.pop() {
                if c == '\n' {
                    continue 'main;
                }
            }
        }

        // Identifiers: keywords, function names, and variables
        if cur.is_ascii_alphabetic() {
            let mut identifier = String::from(cur);
            while let Some(c) = stream.pop() {
                if c.is_ascii_alphanumeric() {
                    identifier.push(c);
                } else {
                    stream.push(c);
                    break;
                }
            }

            tokens.push(match identifier.as_str() {
                "fn" => Token::Fn,
                "let" => Token::Let,
                "f64" => Token::VarType(Type::F64),
                _ => Token::Ident(identifier),
            })
        }

        // Numbers
        if cur.is_ascii_digit() {
            let mut num = String::from(cur);
            while let Some(c) = stream.pop() {
                if c.is_ascii_alphanumeric() {
                    num.push(c);
                } else {
                    stream.push(c);
                    break;
                }
            }

            tokens.push(match num.parse() {
                Ok(n) => Token::Int(n),
                Err(_) => return Err(LexError::InvalidNum),
            });
        }

        // Everything else
        if cur == '+'
            || cur == '-'
            || cur == '*'
            || cur == '/'
            || cur == '^'
            || cur == '>'
            || cur == '<'
        {
            tokens.push(Token::Op(cur));
        } else if cur == '=' {
            tokens.push(Token::Assign);
        } else if cur == ':' {
            tokens.push(Token::Colon);
        } else if cur == ',' {
            tokens.push(Token::Comma);
        } else if cur == '(' {
            tokens.push(Token::OpenParen);
        } else if cur == ')' {
            tokens.push(Token::CloseParen);
        } else if cur == '{' {
            tokens.push(Token::OpenBrace);
        } else if cur == '}' {
            tokens.push(Token::CloseBrace);
        }
    }

    Ok(tokens)
}

/// parser ///
#[derive(Debug, PartialEq)]
pub enum Expression {
    Num {
        value: f64,
    },
    Var {
        name: String,
    },
    BinOp {
        op: char,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },
    Call {
        name: String,
        args: Vec<Expression>,
    },
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Num { value } => write!(f, "{}", value),
            Expression::BinOp { op, lhs, rhs } => write!(f, "({} {} {})", op, lhs, rhs),
            Expression::Var { name } => write!(f, "{}", name),
            Expression::Call { name, args } => {
                let mut s = format!("({}", name);
                if !args.is_empty() {
                    for arg in args {
                        s += &format!(" {}", arg);
                    }
                }
                write!(f, "{})", s)
            }
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Prototype {
    name: String,
    args: Vec<String>,
}

impl Display for Prototype {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = format!("({}", self.name);
        if !self.args.is_empty() {
            for arg in &self.args {
                s += &format!(" {}", arg);
            }
        }
        write!(f, "{})", s)
    }
}

#[derive(Debug, PartialEq)]
pub struct Function {
    proto: Box<Prototype>,
    body: Vec<Expression>,
}

impl Display for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.body.is_empty() {
            write!(f, "(define {})", self.proto)
        } else {
            let s = self.body.iter().fold(String::new(), |mut acc, n| {
                acc += &format!(" {}", n);
                acc
            });
            write!(f, "(define {}{})", self.proto, s)
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum AstNode {
    Expr(Expression),
    Proto(Prototype),
    Func(Function),
}

// Display functions allow us to convert to S-expressions for easier testing.
impl Display for AstNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AstNode::Expr(expr) => write!(f, "{}", expr),
            AstNode::Proto(proto) => write!(f, "{}", proto),
            AstNode::Func(func) => write!(f, "{}", func),
        }
    }
}

enum OpPrec {
    Left(u8),
    Right(u8),
}

impl OpPrec {
    fn prec(op: char) -> Result<OpPrec, String> {
        match op {
            '^' => Ok(OpPrec::Right(4)),
            '*' | '/' => Ok(OpPrec::Left(3)),
            '+' | '-' => Ok(OpPrec::Left(2)),
            '>' | '<' => Ok(OpPrec::Left(1)),
            x => Err(format!("Unknown operator: {}", x)),
        }
    }
}

type ExprParseResult = Result<Expression, String>;
type ProtoParseResult = Result<Prototype, String>;
type FuncParseResult = Result<Function, String>;

pub struct Parser<'a> {
    ast: Vec<AstNode>,
    tokens: std::iter::Peekable<std::slice::Iter<'a, Token>>,
}

impl<'a> Parser<'a> {
    pub fn new(tokens: &'a [Token]) -> Self {
        Parser {
            ast: vec![],
            tokens: tokens.iter().peekable(),
        }
    }

    // Parse each token using recursive descent.
    pub fn parse(mut self) -> Result<Vec<AstNode>, String> {
        while let Some(t) = self.tokens.peek() {
            let node = match t {
                Token::Fn => AstNode::Func(self.parse_function()?),
                _ => AstNode::Expr(self.parse_expression(0)?),
            };
            self.ast.push(node);
        }
        Ok(self.ast)
    }

    // Parses arbitrary length binary expressions. Uses Pratt with op precedence
    // parsing.
    fn parse_expression(&mut self, min_p: u8) -> ExprParseResult {
        // Consume token and load up lhs.
        let mut lhs = self.parse_primary()?;

        // Peek at the next token, otherwise return current lhs.
        while let Some(next) = self.tokens.peek() {
            // Should always be an operator after parse_primary().
            let op = match next {
                Token::Op(op) => op,
                // Start a new expression if we see two primaries in a row.
                _ => break,
            };

            // Determine operator precedence and associativity.
            // Stop eating and return the lhs if the current op:
            //   - is lower precedence than the last one (min_p), or:
            //   - is the same precedence and associates left
            let p = match OpPrec::prec(*op)? {
                OpPrec::Left(p) => {
                    if p <= min_p {
                        break;
                    }
                    p
                }
                OpPrec::Right(p) => {
                    if p < min_p {
                        break;
                    }
                    p
                }
            };

            // Advance past op.
            self.tokens.next();

            // Descend for rhs with the current precedence as min_p.
            let rhs = self.parse_expression(p)?;
            // Make a lhs and continue loop.
            lhs = self.parse_op(*op, lhs, rhs).unwrap();
        }
        Ok(lhs)
    }

    fn parse_function(&mut self) -> FuncParseResult {
        // Eat 'fn'
        self.tokens.next();

        let proto = self.parse_proto()?;

        match self.tokens.next() {
            Some(t @ Token::OpenBrace) => t,
            Some(_) | None => return Err("Expecting '{' in function definition".to_string()),
        };

        // If close brace, body is empty.
        let mut body: Vec<Expression> = vec![];
        if self.tokens.peek().is_some() {
            while let Some(t) = self.tokens.peek() {
                match t {
                    Token::CloseBrace => {
                        self.tokens.next();
                        break;
                    }
                    _ => body.push(self.parse_expression(0)?),
                }
            }
        } else {
            return Err("Expecting '}' in function definition".to_string());
        };

        let node = Function {
            proto: Box::new(proto),
            body,
        };

        Ok(node)
    }

    fn parse_proto(&mut self) -> ProtoParseResult {
        let fn_name = match self.tokens.next() {
            Some(Token::Ident(t)) => t,
            Some(_) | None => return Err("Expecting function name".to_string()),
        };

        match self.tokens.next() {
            Some(t @ Token::OpenParen) => t,
            Some(_) | None => return Err("Expecting '(' in prototype)".to_string()),
        };

        let mut args: Vec<String> = vec![];
        while let Some(&next) = self.tokens.peek() {
            if *next == Token::CloseParen {
                break;
            }

            let id = match self.tokens.next() {
                Some(Token::Ident(t)) => t,
                Some(_) | None => return Err("Expecting identifier in prototype)".to_string()),
            };

            args.push(id.to_string());

            let &next = match self.tokens.peek() {
                Some(t) => t,
                None => return Err("Premature end. Expecting ',' or ')'.".to_string()),
            };

            if *next == Token::CloseParen {
                break;
            } else if *next != Token::Comma {
                return Err(format!("Expecting ','. Got: {}", next));
            }
            // Eat comma
            self.tokens.next();
        }

        // Eat close paren
        self.tokens.next();

        Ok(Prototype {
            name: fn_name.to_string(),
            args,
        })
    }

    // Returns primary expression
    fn parse_primary(&mut self) -> ExprParseResult {
        let node = if let Some(t) = self.tokens.next() {
            match t {
                Token::Int(n) => self.parse_num(*n),
                Token::Ident(id) => self.parse_ident(id),
                Token::OpenParen => self.parse_paren(),
                x => return Err(format!("Expecting primary expression. Got: {}", x)),
            }
        } else {
            unreachable!("parse_primary()");
        };
        node
    }

    fn parse_num(&self, n: f64) -> ExprParseResult {
        Ok(Expression::Num { value: n })
    }

    fn parse_ident(&mut self, id: &str) -> ExprParseResult {
        let node = Expression::Var {
            name: id.to_owned(),
        };

        // If next is not a '(', the current token is just a simple var.
        match self.tokens.peek() {
            Some(t @ Token::OpenParen) => t,
            Some(_) | None => return Ok(node),
        };

        // Eat open paren
        self.tokens.next();

        let mut args: Vec<Expression> = vec![];
        while let Some(&next) = self.tokens.peek() {
            if *next == Token::CloseParen {
                break;
            }

            args.push(self.parse_expression(0)?);

            let &next = match self.tokens.peek() {
                Some(t) => t,
                None => return Err("Premature end. Expecting ',' or ')'.".to_string()),
            };

            if *next == Token::CloseParen {
                break;
            } else if *next != Token::Comma {
                return Err(format!("Expecting ','. Got: {}", next));
            }
            // Eat comma
            self.tokens.next();
        }

        // Eat close paren
        self.tokens.next();

        Ok(Expression::Call {
            name: id.to_owned(),
            args,
        })
    }

    fn parse_op(&self, op: char, lhs: Expression, rhs: Expression) -> ExprParseResult {
        Ok(Expression::BinOp {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        })
    }

    fn parse_paren(&mut self) -> ExprParseResult {
        let lhs = self.parse_expression(0);
        self.tokens.next(); // Eat ')'
        lhs
    }
}

/// IR Generator ///
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::types::BasicMetadataTypeEnum;
use inkwell::values::{AnyValue, BasicValue, FloatValue, FunctionValue, PointerValue};
use inkwell::FloatPredicate;
use std::collections::HashMap;

enum IrRetVal<'ctx> {
    Expr(FloatValue<'ctx>),
    Func(FunctionValue<'ctx>),
}

type ExprIrResult<'ctx> = Result<FloatValue<'ctx>, String>;
type FuncIrResult<'ctx> = Result<FunctionValue<'ctx>, String>;

// TODO: Think about some tests for IR generation.
pub struct IrGenerator<'a, 'ctx> {
    context: &'ctx Context,
    builder: &'a Builder<'ctx>,
    module: &'a Module<'ctx>,
    values: HashMap<String, PointerValue<'ctx>>,
}

impl<'a, 'ctx> IrGenerator<'a, 'ctx> {
    pub fn new(
        context: &'ctx Context,
        builder: &'a Builder<'ctx>,
        module: &'a Module<'ctx>,
    ) -> Self {
        let values = HashMap::new();
        IrGenerator {
            context,
            builder,
            module,
            values,
        }
    }

    // taken from inkwell example
    // todo: figure out what this is
    fn create_entry_block_alloca(&self, name: &str, func: &FunctionValue) -> PointerValue<'ctx> {
        let builder = self.context.create_builder();

        let entry = func.get_first_basic_block().unwrap();

        match entry.get_first_instruction() {
            Some(first_instr) => builder.position_before(&first_instr),
            None => builder.position_at_end(entry),
        }

        builder.build_alloca(self.context.f64_type(), name)
    }

    // Iterate over all nodes and generate IR. Optionally return a string (for
    // testing).
    pub fn generate(&mut self, ast: &[AstNode], is_debug: bool) -> Result<Option<String>, String> {
        for node in ast {
            let ir = match node {
                AstNode::Expr(expr) => IrRetVal::Expr(self.gen_expr_ir(expr)?),
                AstNode::Proto(proto) => IrRetVal::Func(self.gen_proto_ir(proto)?),
                AstNode::Func(func) => IrRetVal::Func(self.gen_func_ir(func)?),
            };

            if is_debug {
                if let IrRetVal::Func(f) = ir {
                    let output = f.print_to_string().to_string();
                    f.print_to_stderr();
                    return Ok(Some(output));
                }
            }
        }
        Ok(None)
    }

    fn gen_expr_ir(&self, expr: &Expression) -> ExprIrResult<'ctx> {
        match expr {
            Expression::Num { value: v } => self.gen_num_ir(*v),
            Expression::Var { name: n } => self.gen_var_ir(n),
            Expression::BinOp { op, lhs, rhs } => self.gen_binop_ir(*op, lhs, rhs),
            Expression::Call { name, args } => self.gen_call_ir(name, args),
        }
    }

    fn gen_num_ir(&self, num: f64) -> ExprIrResult<'ctx> {
        Ok(self.context.f64_type().const_float(num))
    }

    fn gen_var_ir(&self, name: &str) -> ExprIrResult<'ctx> {
        match self.values.get(name) {
            Some(var) => Ok(self.builder.build_load(*var, name).into_float_value()),
            None => Err(format!("Unknown variable: {}", name)),
        }
    }

    fn gen_binop_ir(&self, op: char, lhs: &Expression, rhs: &Expression) -> ExprIrResult<'ctx> {
        let lhs = self.gen_expr_ir(lhs)?;
        let rhs = self.gen_expr_ir(rhs)?;

        match op {
            '*' => Ok(self.builder.build_float_mul(lhs, rhs, "tmpmul")),
            '/' => Ok(self.builder.build_float_div(lhs, rhs, "tmpdiv")),
            '+' => Ok(self.builder.build_float_add(lhs, rhs, "tmpadd")),
            '-' => Ok(self.builder.build_float_sub(lhs, rhs, "tmpsub")),
            op @ ('>' | '<') => {
                let res = if op == '>' {
                    self.builder
                        .build_float_compare(FloatPredicate::UGT, lhs, rhs, "tmpcmp")
                } else {
                    self.builder
                        .build_float_compare(FloatPredicate::ULT, lhs, rhs, "tmpcmp")
                };
                Ok(self.builder.build_unsigned_int_to_float(
                    res,
                    self.context.f64_type(),
                    "tmpbool",
                ))
            }
            x => Err(format!("Unknown binary operator: {}", x)),
        }
    }

    fn gen_call_ir(&self, name: &str, args: &[Expression]) -> ExprIrResult<'ctx> {
        let func = match self.module.get_function(name) {
            Some(f) => f,
            None => return Err(format!("Unknown function call: {}", name)),
        };

        let mut args_ir = Vec::with_capacity(args.len());
        for arg in args {
            args_ir.push(self.gen_expr_ir(arg)?.into());
        }

        match self
            .builder
            .build_call(func, &args_ir, "tmpcall")
            .try_as_basic_value()
            .left()
        {
            Some(v) => Ok(v.into_float_value()),
            None => Err(String::from("Invalid call?")),
        }
    }

    fn gen_proto_ir(&self, proto: &Prototype) -> FuncIrResult<'ctx> {
        let f64_type = self.context.f64_type();
        let args_type = proto
            .args
            .iter()
            .map(|_| f64_type.into())
            .collect::<Vec<BasicMetadataTypeEnum>>();

        let func_type = f64_type.fn_type(&args_type, false);
        let func = self.module.add_function(&proto.name, func_type, None);

        func.get_param_iter().enumerate().for_each(|(i, arg)| {
            arg.into_float_value().set_name(&proto.args[i]);
        });

        Ok(func)
    }

    fn gen_func_ir(&mut self, func: &Function) -> FuncIrResult<'ctx> {
        let function = self.gen_proto_ir(&func.proto)?;

        // todo: check for externs

        let bb = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(bb);

        self.values.reserve(func.proto.args.len());
        for (i, arg) in function.get_param_iter().enumerate() {
            let arg_name = &func.proto.args[i];
            let alloca = self.create_entry_block_alloca(arg_name, &function);
            self.builder.build_store(alloca, arg);
            self.values.insert(arg_name.to_owned(), alloca);
        }

        let mut last_expr: Option<Box<dyn BasicValue>> = None;
        for e in &func.body {
            last_expr = Some(Box::new(self.gen_expr_ir(e)?));
        }
        self.builder.build_return(last_expr.as_deref());

        if function.verify(true) {
            Ok(function)
        } else {
            unsafe {
                // TODO: Do we care about this for AOT comiplation?
                function.delete();
            }
            Err(String::from("Bad function generation"))
        }
    }
}
