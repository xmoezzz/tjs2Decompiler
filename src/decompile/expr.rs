use std::fmt;

use super::ssa::{Var, VarId};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    Not,
    BitNot,
    Num,
    CharCode,
    CharFromCode,
    Typeof,
    Delete,
    Int,
    Real,
    String,
    Octet,
    Invalidate,
    IsValid,
    /// TJS unary `&`: access the underlying property substance, bypassing getter/setter dispatch.
    IgnoreProp,
}

impl UnOp {
    pub fn op_str(self) -> &'static str {
        match self {
            UnOp::Neg => "-",
            UnOp::Not => "!",
            UnOp::BitNot => "~",
            UnOp::Num => "+",
            UnOp::CharCode => "#",
            UnOp::CharFromCode => "$",
            UnOp::Typeof => "typeof",
            UnOp::Delete => "delete",
            UnOp::Int => "int",
            UnOp::Real => "real",
            UnOp::String => "string",
            UnOp::Octet => "octet",
            UnOp::Invalidate => "invalidate",
            UnOp::IsValid => "isvalid",
            UnOp::IgnoreProp => "&",
        }
    }

    pub fn needs_space(self) -> bool {
        matches!(
            self,
            UnOp::Typeof
                | UnOp::Delete
                | UnOp::Int
                | UnOp::Real
                | UnOp::String
                | UnOp::Octet
                | UnOp::Invalidate
                | UnOp::IsValid
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    IDiv,
    Mod,

    Shl,
    Shr,
    UShr,

    Lt,
    Le,
    Gt,
    Ge,

    In,
    InstanceOf,

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
    IDivAssign,
    ModAssign,
    ShlAssign,
    ShrAssign,
    UShrAssign,
    AndAssign,
    OrAssign,
    XorAssign,
    LogAndAssign,
    LogOrAssign,

    InContextOf,
}

impl BinOp {
    pub fn op_str(self) -> &'static str {
        match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::IDiv => "\\",
            BinOp::Mod => "%",

            BinOp::Shl => "<<",
            BinOp::Shr => ">>",
            BinOp::UShr => ">>>",

            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",

            BinOp::In => "in",
            BinOp::InstanceOf => "instanceof",

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
            BinOp::IDivAssign => "\\=",
            BinOp::ModAssign => "%=",
            BinOp::ShlAssign => "<<=",
            BinOp::ShrAssign => ">>=",
            BinOp::UShrAssign => ">>>=",
            BinOp::AndAssign => "&=",
            BinOp::OrAssign => "|=",
            BinOp::XorAssign => "^=",
            BinOp::LogAndAssign => "&&=",
            BinOp::LogOrAssign => "||=",
            BinOp::InContextOf => "incontextof",
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
            | BinOp::IDivAssign
            | BinOp::ModAssign
            | BinOp::ShlAssign
            | BinOp::ShrAssign
            | BinOp::UShrAssign
            | BinOp::AndAssign
            | BinOp::OrAssign
            | BinOp::XorAssign
            | BinOp::LogAndAssign
            | BinOp::LogOrAssign => 0,

            BinOp::LogOr => 1,
            BinOp::LogAnd => 2,

            BinOp::BitOr => 3,
            BinOp::BitXor => 4,
            BinOp::BitAnd => 5,

            BinOp::Eq | BinOp::Ne | BinOp::StrictEq | BinOp::StrictNe => 6,

            BinOp::Lt
            | BinOp::Le
            | BinOp::Gt
            | BinOp::Ge
            | BinOp::In
            | BinOp::InstanceOf
            | BinOp::InContextOf => 7,

            BinOp::Shl | BinOp::Shr | BinOp::UShr => 8,

            BinOp::Add | BinOp::Sub => 9,

            BinOp::Mul | BinOp::Div | BinOp::IDiv | BinOp::Mod => 10,
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
                | BinOp::IDivAssign
                | BinOp::ModAssign
                | BinOp::ShlAssign
                | BinOp::ShrAssign
                | BinOp::UShrAssign
                | BinOp::AndAssign
                | BinOp::OrAssign
                | BinOp::XorAssign
                | BinOp::LogAndAssign
                | BinOp::LogOrAssign
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
    ObjectRef(i32),
    GeneratorRef(i32),

    /// VM register %-2.  This is not `global` and not `this`: it is the TJS
    /// scope proxy that dispatches to `this` first and then to `global`.
    /// It may only be lowered back to source when the surrounding operation
    /// has an exact source spelling (for example a bare identifier).
    ScopeProxy,

    Unary(UnOp, Box<Expr>),
    Deref(Box<Expr>),

    Binary(BinOp, Box<Expr>, Box<Expr>),

    /// Source conditional expression.  Keep this as an explicit IR node
    /// instead of spelling it as opaque text so SSA/dataflow rewrites can
    /// continue to inspect all three operands and their effects.
    Conditional {
        cond: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
    },

    Call(Box<Expr>, Vec<Expr>),
    New(Box<Expr>, Vec<Expr>),

    /// Source-level inline Array/Dictionary literals.  The compiler lowers
    /// these to `new global.Array/Dictionary` plus ordered SPIS stores; keep
    /// them explicit once that exact builder pattern has been recognized.
    ArrayLiteral(Vec<Expr>),
    DictionaryLiteral(Vec<(Expr, Expr)>),

    /// Source-level RegExp literal, reconstructed only from the exact compiler
    /// template `new global.RegExp(); obj._compile(internal_pattern)`.
    /// The stored string is the complete TJS source token, e.g. `/foo/gi`.
    RegExpLiteral(String),

    // TJS2 call-argument forms that cannot be represented as ordinary value
    // expressions.  These are only emitted inside Call/New/MethodCall args.
    // `x*` expands an explicit array-like argument, `*` expands unnamed
    // arguments, and `...` forwards the current function arguments verbatim.
    ArgExpand(Box<Expr>),
    ArgUnnamedExpand,
    ArgForwardAll,

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
            | Expr::Octet(_)
            | Expr::ObjectRef(_)
            | Expr::GeneratorRef(_)
            | Expr::ScopeProxy
            | Expr::ArrayLiteral(_)
            | Expr::DictionaryLiteral(_)
            | Expr::RegExpLiteral(_)
            | Expr::Conditional { .. }
            | Expr::ArgUnnamedExpand
            | Expr::ArgForwardAll => 20,

            Expr::ArgExpand(..) => 19,

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
                    write!(f, "__tjs2dec_unrepresentable_scope_proxy")?
                } else if *r == -1 {
                    write!(f, "this")?
                } else {
                    write!(f, "r{}", r)?
                }
            }
            Expr::Flag => write!(f, "flag")?,
            Expr::ConstData(i) => write!(f, "__d[{}]", i)?,

            Expr::SsaVar(v) => write!(f, "{}", fmt_var(*v))?,

            Expr::Void => write!(f, "void")?,
            Expr::Null => write!(f, "null")?,
            Expr::Bool(b) => write!(f, "{}", if *b { "true" } else { "false" })?,
            Expr::Int(i) => write!(f, "{}", i)?,
            Expr::Real(x) => {
                // Rust's Debug formatter uses a shortest round-trippable decimal
                // and, unlike Display, keeps an integral-valued real as `1.0`.
                // TJS also has exact source spellings for infinities and for
                // its canonical quiet NaN.  Preserve NaN sign and reject any
                // non-canonical payload rather than silently normalizing bits.
                if x.is_finite() {
                    write!(f, "{:?}", x)?;
                } else {
                    match x.to_bits() {
                        0x7ff0_0000_0000_0000 => write!(f, "Infinity")?,
                        0xfff0_0000_0000_0000 => write!(f, "-Infinity")?,
                        0x7ff8_0000_0000_0000 => write!(f, "NaN")?,
                        0xfff8_0000_0000_0000 => write!(f, "-NaN")?,
                        _ => write!(f, "__tjs2dec_unrepresentable_real_literal")?,
                    }
                }
            }
            Expr::Str(s) => write!(f, "\"{}\"", escape_tjs_string(s))?,
            Expr::ObjectRef(idx) => write!(f, "__tjs2dec_obj_{}", idx)?,
            Expr::GeneratorRef(idx) => write!(f, "__tjs2dec_gen_{}", idx)?,
            Expr::ScopeProxy => write!(f, "__tjs2dec_unrepresentable_scope_proxy")?,
            Expr::Octet(bytes) => {
                write!(f, "<%")?;
                for b in bytes {
                    write!(f, " {:02x}", b)?;
                }
                if !bytes.is_empty() {
                    write!(f, " ")?;
                }
                write!(f, "%>")?;
            }

            Expr::Unary(op, e) => {
                if *op == UnOp::IgnoreProp {
                    write!(f, "&(")?;
                    e.fmt_with_prec(f, 0, fmt_var)?;
                    write!(f, ")")?;
                } else {
                    if op.needs_space() {
                        write!(f, "{} ", op.op_str())?;
                    } else {
                        write!(f, "{}", op.op_str())?;
                    }
                    e.fmt_with_prec(f, my_prec, fmt_var)?;
                }
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

            Expr::Conditional {
                cond,
                then_expr,
                else_expr,
            } => {
                // Parenthesize the complete conditional unconditionally.  It
                // avoids depending on small precedence differences between
                // TJS versions and makes nested conditional reconstruction
                // unambiguous without changing evaluation order.
                write!(f, "(")?;
                cond.fmt_with_prec(f, 0, fmt_var)?;
                write!(f, " ? ")?;
                then_expr.fmt_with_prec(f, 0, fmt_var)?;
                write!(f, " : ")?;
                else_expr.fmt_with_prec(f, 0, fmt_var)?;
                write!(f, ")")?;
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

            Expr::ArrayLiteral(items) => {
                write!(f, "[")?;
                for (i, item) in items.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    item.fmt_with_prec(f, 0, fmt_var)?;
                }
                write!(f, "]")?;
            }

            Expr::DictionaryLiteral(items) => {
                write!(f, "%[")?;
                for (i, (key, value)) in items.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    key.fmt_with_prec(f, 0, fmt_var)?;
                    write!(f, " => ")?;
                    value.fmt_with_prec(f, 0, fmt_var)?;
                }
                write!(f, "]")?;
            }

            Expr::RegExpLiteral(source) => write!(f, "{}", source)?,

            Expr::ArgExpand(expr) => {
                expr.fmt_with_prec(f, 19, fmt_var)?;
                write!(f, "*")?;
            }
            Expr::ArgUnnamedExpand => write!(f, "*")?,
            Expr::ArgForwardAll => write!(f, "...")?,

            Expr::Index(base, key) => {
                if matches!(base.as_ref(), Expr::ScopeProxy) {
                    // There is no source-level expression denoting the proxy itself.
                    // Keep an unmistakable invalid sentinel; the semantic audit rejects
                    // this before source is returned to the caller.
                    write!(f, "__tjs2dec_unrepresentable_scope_proxy[")?;
                    key.fmt_with_prec(f, 0, fmt_var)?;
                    write!(f, "]")?;
                } else {
                    base.fmt_with_prec(f, 19, fmt_var)?;
                    write!(f, "[")?;
                    key.fmt_with_prec(f, 0, fmt_var)?;
                    write!(f, "]")?;
                }
            }

            Expr::Member(base, member) => {
                if matches!(base.as_ref(), Expr::ScopeProxy) {
                    // `% -2 .*name` is a source-level bare identifier only if
                    // it cannot be captured by one of our synthetic lexical
                    // bindings (and is itself legal as an identifier).
                    if scope_proxy_ident_is_safe(member) {
                        write!(f, "{}", member)?;
                    } else {
                        write!(f, "__tjs2dec_unrepresentable_scope_proxy")?;
                    }
                } else {
                    base.fmt_with_prec(f, 19, fmt_var)?;
                    write!(f, ".{}", member)?;
                }
            }

            Expr::MethodCall { base, member, args } => {
                if matches!(base.as_ref(), Expr::ScopeProxy) {
                    if scope_proxy_ident_is_safe(member) {
                        write!(f, "{}(", member)?;
                    } else {
                        write!(f, "__tjs2dec_unrepresentable_scope_proxy(")?;
                    }
                } else {
                    base.fmt_with_prec(f, 19, fmt_var)?;
                    write!(f, ".{}(", member)?;
                }
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
        Var::Reg(r) => {
            if r <= -3 {
                format!("a{}", -3 - r)
            } else if r == -2 {
                "__tjs2dec_unrepresentable_scope_proxy".to_string()
            } else if r == -1 {
                "this".to_string()
            } else {
                format!("r{}#{}", r, vid.ver)
            }
        }
        Var::Flag => format!("flag#{}", vid.ver),
        Var::Result => format!("result#{}", vid.ver),
        Var::Exception => format!("exc#{}", vid.ver),
    }
}

pub fn generated_ident_collision(s: &str) -> bool {
    if s.starts_with("__tjs2dec_") {
        return true;
    }
    fn digits_after<'a>(s: &'a str, prefix: &str) -> Option<&'a str> {
        let rest = s.strip_prefix(prefix)?;
        if !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit()) {
            Some(rest)
        } else {
            None
        }
    }
    if digits_after(s, "a").is_some()
        || digits_after(s, "_fr").is_some()
        || digits_after(s, "flag_").is_some()
        || digits_after(s, "exc_").is_some()
    {
        return true;
    }
    if let Some(rest) = s.strip_prefix('r') {
        if let Some((reg, ver)) = rest.split_once('_') {
            if !reg.is_empty()
                && !ver.is_empty()
                && reg.bytes().all(|b| b.is_ascii_digit())
                && ver.bytes().all(|b| b.is_ascii_digit())
            {
                return true;
            }
        }
    }
    false
}

fn is_tjs_keyword(s: &str) -> bool {
    matches!(
        s,
        "break" | "continue" | "const" | "catch" | "class" | "case" | "debugger"
            | "default" | "delete" | "do" | "else" | "export" | "extends" | "finally"
            | "for" | "function" | "global" | "if" | "import" | "in" | "incontextof"
            | "instanceof" | "int" | "invalidate" | "isvalid" | "new" | "octet"
            | "property" | "private" | "protected" | "public" | "real" | "return"
            | "static" | "string" | "super" | "switch" | "synchronized" | "this"
            | "throw" | "try" | "typeof" | "var" | "void" | "while" | "with"
            | "true" | "false" | "null"
    )
}

fn scope_proxy_ident_is_safe(s: &str) -> bool {
    let mut chars = s.chars();
    let Some(first) = chars.next() else { return false; };
    (first == '_' || first.is_ascii_alphabetic())
        && chars.all(|c| c == '_' || c.is_ascii_alphanumeric())
        && !generated_ident_collision(s)
        && !is_tjs_keyword(s)
}

fn escape_tjs_string(s: &str) -> String {
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

#[cfg(test)]
mod tests {
    use super::{BinOp, Expr, UnOp};

    #[test]
    fn renders_tjs_vm_unary_operators() {
        assert_eq!(
            Expr::Unary(UnOp::CharCode, Box::new(Expr::Str("A".into()))).to_tjs(),
            "#\"A\""
        );
        assert_eq!(
            Expr::Unary(UnOp::CharFromCode, Box::new(Expr::Int(65))).to_tjs(),
            "$65"
        );
        assert_eq!(
            Expr::Unary(UnOp::Num, Box::new(Expr::Str("123".into()))).to_tjs(),
            "+\"123\""
        );
        assert_eq!(
            Expr::Unary(UnOp::Invalidate, Box::new(Expr::Reg(1))).to_tjs(),
            "invalidate r1"
        );
        assert_eq!(
            Expr::Unary(UnOp::IsValid, Box::new(Expr::Reg(1))).to_tjs(),
            "isvalid r1"
        );
    }

    #[test]
    fn renders_integer_division() {
        assert_eq!(
            Expr::Binary(BinOp::IDiv, Box::new(Expr::Int(7)), Box::new(Expr::Int(3))).to_tjs(),
            "7 \\ 3"
        );
    }

    #[test]
    fn renders_instanceof_and_incontextof() {
        assert_eq!(
            Expr::Binary(
                BinOp::InstanceOf,
                Box::new(Expr::Reg(1)),
                Box::new(Expr::Str("Array".into())),
            )
            .to_tjs(),
            "r1 instanceof \"Array\""
        );
        assert_eq!(
            Expr::Binary(
                BinOp::InContextOf,
                Box::new(Expr::Reg(1)),
                Box::new(Expr::Reg(-1)),
            )
            .to_tjs(),
            "r1 incontextof this"
        );
    }

    #[test]
    fn renders_inline_collection_literals() {
        assert_eq!(
            Expr::ArrayLiteral(vec![Expr::Int(1), Expr::Str("x".into())]).to_tjs(),
            "[1, \"x\"]"
        );
        assert_eq!(
            Expr::DictionaryLiteral(vec![
                (Expr::Str("a".into()), Expr::Int(1)),
                (Expr::Str("b".into()), Expr::Int(2)),
            ])
            .to_tjs(),
            "%[\"a\" => 1, \"b\" => 2]"
        );
    }

    #[test]
    fn renders_exact_tjs_nonfinite_literals() {
        assert_eq!(Expr::Real(f64::INFINITY).to_tjs(), "Infinity");
        assert_eq!(Expr::Real(f64::NEG_INFINITY).to_tjs(), "-Infinity");
        assert_eq!(Expr::Real(f64::from_bits(0x7ff8_0000_0000_0000)).to_tjs(), "NaN");
        assert_eq!(Expr::Real(f64::from_bits(0xfff8_0000_0000_0000)).to_tjs(), "-NaN");
        assert_eq!(
            Expr::Real(f64::from_bits(0x7ff8_0000_0000_0001)).to_tjs(),
            "__tjs2dec_unrepresentable_real_literal"
        );
    }

    #[test]
    fn renders_tjs_extended_call_arguments() {
        let call = Expr::Call(
            Box::new(Expr::Reg(1)),
            vec![
                Expr::Reg(2),
                Expr::ArgExpand(Box::new(Expr::Reg(3))),
                Expr::ArgUnnamedExpand,
            ],
        );
        assert_eq!(call.to_tjs(), "r1(r2, r3*, *)");

        let forwarded = Expr::Call(Box::new(Expr::Reg(1)), vec![Expr::ArgForwardAll]);
        assert_eq!(forwarded.to_tjs(), "r1(...)");
    }

}
