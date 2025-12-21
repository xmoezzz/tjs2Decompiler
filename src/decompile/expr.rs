use std::fmt;

use super::ssa::{Var, VarId};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    Not,
    BitNot,
    Typeof,
    Delete,
}

impl UnOp {
    pub fn op_str(self) -> &'static str {
        match self {
            UnOp::Neg => "-",
            UnOp::Not => "!",
            UnOp::BitNot => "~",
            UnOp::Typeof => "typeof",
            UnOp::Delete => "delete",
        }
    }

    pub fn needs_space(self) -> bool {
        matches!(self, UnOp::Typeof | UnOp::Delete)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,

    Shl,
    Shr,
    UShr,

    Lt,
    Le,
    Gt,
    Ge,

    In,

    Eq,
    Ne,
    StrictEq,
    StrictNe,

    BitAnd,
    BitOr,
    BitXor,

    LogAnd,
    LogOr,

    Assign,

    AddAssign,
    SubAssign,
    MulAssign,
    DivAssign,
    ModAssign,
    ShlAssign,
    ShrAssign,
    UShrAssign,
    AndAssign,
    OrAssign,
    XorAssign,
}

impl BinOp {
    pub fn op_str(self) -> &'static str {
        match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Mod => "%",

            BinOp::Shl => "<<",
            BinOp::Shr => ">>",
            BinOp::UShr => ">>>",

            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",

            BinOp::In => "in",

            BinOp::Eq => "==",
            BinOp::Ne => "!=",
            BinOp::StrictEq => "===",
            BinOp::StrictNe => "!==",

            BinOp::BitAnd => "&",
            BinOp::BitOr => "|",
            BinOp::BitXor => "^",

            BinOp::LogAnd => "&&",
            BinOp::LogOr => "||",

            BinOp::Assign => "=",

            BinOp::AddAssign => "+=",
            BinOp::SubAssign => "-=",
            BinOp::MulAssign => "*=",
            BinOp::DivAssign => "/=",
            BinOp::ModAssign => "%=",
            BinOp::ShlAssign => "<<=",
            BinOp::ShrAssign => ">>=",
            BinOp::UShrAssign => ">>>=",
            BinOp::AndAssign => "&=",
            BinOp::OrAssign => "|=",
            BinOp::XorAssign => "^=",
        }
    }

    // Higher = tighter
    pub fn precedence(self) -> u8 {
        match self {
            BinOp::Assign
            | BinOp::AddAssign
            | BinOp::SubAssign
            | BinOp::MulAssign
            | BinOp::DivAssign
            | BinOp::ModAssign
            | BinOp::ShlAssign
            | BinOp::ShrAssign
            | BinOp::UShrAssign
            | BinOp::AndAssign
            | BinOp::OrAssign
            | BinOp::XorAssign => 0,

            BinOp::LogOr => 1,
            BinOp::LogAnd => 2,

            BinOp::BitOr => 3,
            BinOp::BitXor => 4,
            BinOp::BitAnd => 5,

            BinOp::Eq | BinOp::Ne | BinOp::StrictEq | BinOp::StrictNe => 6,

            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::In => 7,

            BinOp::Shl | BinOp::Shr | BinOp::UShr => 8,

            BinOp::Add | BinOp::Sub => 9,

            BinOp::Mul | BinOp::Div | BinOp::Mod => 10,
        }
    }

    pub fn tightens_right(self) -> bool {
        matches!(
            self,
            BinOp::Assign
                | BinOp::AddAssign
                | BinOp::SubAssign
                | BinOp::MulAssign
                | BinOp::DivAssign
                | BinOp::ModAssign
                | BinOp::ShlAssign
                | BinOp::ShrAssign
                | BinOp::UShrAssign
                | BinOp::AndAssign
                | BinOp::OrAssign
                | BinOp::XorAssign
        )
    }
}

#[derive(Debug, Clone)]
pub enum Expr {
    // Raw / non-SSA forms (sometimes useful)
    Reg(i32),
    Flag,
    ConstData(i32),

    // SSA form used by expr_build.rs
    SsaVar(VarId),

    Void,
    Null,
    Bool(bool),
    Int(i64),
    Real(f64),
    Str(String),
    Octet(Vec<u8>),

    Unary(UnOp, Box<Expr>),
    Deref(Box<Expr>),

    Binary(BinOp, Box<Expr>, Box<Expr>),

    Call(Box<Expr>, Vec<Expr>),
    New(Box<Expr>, Vec<Expr>),

    Index(Box<Expr>, Box<Expr>),
    Member(Box<Expr>, String),

    MethodCall {
        base: Box<Expr>,
        member: String,
        args: Vec<Expr>,
    },

    Opaque(String, Vec<Expr>),
}

impl Expr {
    pub fn to_tjs(&self) -> String {
        self.to_tjs_with(&fmt_vid_default)
    }

    pub fn to_tjs_with(&self, fmt_var: &dyn Fn(VarId) -> String) -> String {
        let mut out = String::new();
        self.fmt_with_prec(&mut out, 0, fmt_var)
            .expect("fmt never fails for String");
        out
    }

    fn precedence(&self) -> u8 {
        match self {
            Expr::Reg(_)
            | Expr::Flag
            | Expr::ConstData(_)
            | Expr::SsaVar(_)
            | Expr::Void
            | Expr::Null
            | Expr::Bool(_)
            | Expr::Int(_)
            | Expr::Real(_)
            | Expr::Str(_)
            | Expr::Octet(_) => 20,

            Expr::Member(..) | Expr::Index(..) | Expr::Call(..) | Expr::MethodCall { .. } => 19,

            Expr::New(..) => 18,

            Expr::Unary(..) | Expr::Deref(..) => 17,

            Expr::Binary(op, ..) => op.precedence(),
            Expr::Opaque(_, _) => 1,
        }
    }

    fn fmt_with_prec(
        &self,
        f: &mut dyn fmt::Write,
        outer_prec: u8,
        fmt_var: &dyn Fn(VarId) -> String,
    ) -> fmt::Result {
        let my_prec = self.precedence();
        let needs_paren = my_prec < outer_prec;

        if needs_paren {
            write!(f, "(")?;
        }

        match self {
            Expr::Reg(r) => {
                // write!(f, "r{}", r)?
                if *r <= -3 {
                    write!(f, "a{}", -3 - r)?
                } else if *r == -2 {
                    write!(f, "global")?
                } else if *r == -1 {
                    write!(f, "this")?
                } else {
                    write!(f, "r{}", r)?
                }
            },
            Expr::Flag => write!(f, "flag")?,
            Expr::ConstData(i) => write!(f, "__d[{}]", i)?,

            Expr::SsaVar(v) => {
                // write!(f, "{}", fmt_var(*v))?
                match v.var {
                    Var::Reg(r) => {
                        if r <= -3 {
                            write!(f, "a{}", -3 - r)?
                        } else if r == -2 {
                            write!(f, "global")?
                        } else if r == -1 {
                            write!(f, "this")?
                        } else {
                            write!(f, "{}", fmt_var(*v))?
                        }
                    },
                    _ => {
                        write!(f, "{}", fmt_var(*v))?
                    }
                }
            },

            Expr::Void => write!(f, "void")?,
            Expr::Null => write!(f, "null")?,
            Expr::Bool(b) => write!(f, "{}", if *b { "true" } else { "false" })?,
            Expr::Int(i) => write!(f, "{}", i)?,
            Expr::Real(x) => write!(f, "{}", x)?,
            Expr::Str(s) => write!(f, "\"{}\"", escape_tjs_string(s))?,
            Expr::Octet(bytes) => {
                if bytes.is_empty() {
                    write!(f, "octet(0)")?;
                } else {
                    let mut preview = String::new();
                    let n = bytes.len().min(16);
                    for (i, b) in bytes.iter().take(n).enumerate() {
                        if i != 0 {
                            preview.push(' ');
                        }
                        preview.push_str(&format!("{:02x}", b));
                    }
                    if bytes.len() > n {
                        write!(f, "octet(len={}, head={})", bytes.len(), preview)?;
                    } else {
                        write!(f, "octet(len={}, bytes={})", bytes.len(), preview)?;
                    }
                }
            }

            Expr::Unary(op, e) => {
                if op.needs_space() {
                    write!(f, "{} ", op.op_str())?;
                } else {
                    write!(f, "{}", op.op_str())?;
                }
                e.fmt_with_prec(f, my_prec, fmt_var)?;
            }

            Expr::Deref(e) => {
                write!(f, "*")?;
                e.fmt_with_prec(f, my_prec, fmt_var)?;
            }

            Expr::Binary(op, l, r) => {
                let lp = op.precedence();
                let rp = if op.tightens_right() { lp } else { lp + 1 };
                l.fmt_with_prec(f, lp, fmt_var)?;
                write!(f, " {} ", op.op_str())?;
                r.fmt_with_prec(f, rp, fmt_var)?;
            }

            Expr::Call(callee, args) => {
                callee.fmt_with_prec(f, 19, fmt_var)?;
                write!(f, "(")?;
                for (i, a) in args.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    a.fmt_with_prec(f, 0, fmt_var)?;
                }
                write!(f, ")")?;
            }

            Expr::New(callee, args) => {
                write!(f, "new ")?;
                callee.fmt_with_prec(f, 19, fmt_var)?;
                write!(f, "(")?;
                for (i, a) in args.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    a.fmt_with_prec(f, 0, fmt_var)?;
                }
                write!(f, ")")?;
            }

            Expr::Index(base, key) => {
                base.fmt_with_prec(f, 19, fmt_var)?;
                write!(f, "[")?;
                key.fmt_with_prec(f, 0, fmt_var)?;
                write!(f, "]")?;
            }

            Expr::Member(base, member) => {
                base.fmt_with_prec(f, 19, fmt_var)?;
                write!(f, ".{}", member)?;
            }

            Expr::MethodCall { base, member, args } => {
                base.fmt_with_prec(f, 19, fmt_var)?;
                write!(f, ".{}(", member)?;
                for (i, a) in args.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    a.fmt_with_prec(f, 0, fmt_var)?;
                }
                write!(f, ")")?;
            }

            Expr::Opaque(name, args) => {
                if args.is_empty() {
                    write!(f, "{}", name)?;
                } else {
                    write!(f, "{}(", name)?;
                    for (i, a) in args.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        a.fmt_with_prec(f, 0, fmt_var)?;
                    }
                    write!(f, ")")?;
                }
            }
        }

        if needs_paren {
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_tjs())
    }
}

fn fmt_vid_default(vid: VarId) -> String {
    match vid.var {
        Var::Reg(r) => format!("r{}#{}", r, vid.ver),
        Var::Flag => format!("flag#{}", vid.ver),
        Var::Exception => format!("exc#{}", vid.ver),
    }
}

pub fn escape_tjs_string(s: &str) -> String {
    let mut out = String::new();
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\0' => out.push_str("\\0"),
            _ => out.push(c),
        }
    }
    out
}
