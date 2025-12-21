use std::fmt;

#[derive(Debug, Clone)]
pub struct Tjs2File {
    pub toplevel: i32,
    pub const_pools: ConstPools,
    pub objects: Vec<Tjs2Object>,
}

#[derive(Debug, Clone, Default)]
pub struct ConstPools {
    pub bytes: Vec<i8>,
    pub shorts: Vec<i16>,
    pub ints: Vec<i32>,
    pub longs: Vec<i64>,
    pub doubles: Vec<f64>,
    pub strings: Vec<String>,
    pub octets: Vec<Vec<u8>>,
}

#[derive(Debug, Clone)]
pub struct Tjs2Object {
    pub index: usize,

    pub parent: i32,
    pub name_string_index: i32,
    pub name: Option<String>,
    pub context_type: i32,

    pub max_variable_count: i32,
    pub variable_reserve_count: i32,
    pub max_frame_count: i32,
    pub func_decl_arg_count: i32,
    pub func_decl_unnamed_arg_array_base: i32,
    pub func_decl_collapse_base: i32,

    pub prop_setter: i32,
    pub prop_getter: i32,
    pub super_class_getter: i32,

    pub code: Vec<i32>,                 // i16 words, sign-extended to i32
    pub data: Vec<Variant>,             // vdata[]
    pub scgetterps: Vec<i32>,           // unused for now
    pub properties: Vec<(i32, i32)>,    // (name_string_index, object_index)
}

#[derive(Debug, Clone)]
pub enum Variant {
    Void,
    NullObject,           // TYPE_OBJECT (krkrz uses this mainly for null closure in bytecode)
    InterObject(i32),     // TYPE_INTER_OBJECT
    InterGenerator(i32),  // TYPE_INTER_GENERATOR
    String(i32),          // index into string pool
    Octet(i32),           // index into octet pool
    Real(i32),            // index into double pool
    Byte(i32),            // index into byte pool
    Short(i32),           // index into short pool
    Integer(i32),         // index into int pool
    Long(i32),            // index into long pool
    Unknown,
}

impl Variant {
    pub fn to_readable(&self, pools: &ConstPools) -> String {
        match *self {
            Variant::Void => "void".to_string(),
            Variant::NullObject => "null".to_string(),
            Variant::InterObject(idx) => format!("#InterObject({})", idx),
            Variant::InterGenerator(idx) => format!("#InterGenerator({})", idx),
            Variant::String(i) => {
                let s = pools.strings.get(i as usize).cloned().unwrap_or_else(|| "<bad-string-index>".to_string());
                format!("#Var.String({})", fmt_quoted(&s))
            }
            Variant::Octet(i) => {
                let n = pools.octets.get(i as usize).map(|b| b.len()).unwrap_or(0);
                format!("#Var.Octet(len={})", n)
            }
            Variant::Real(i) => {
                let v = pools.doubles.get(i as usize).cloned().unwrap_or(f64::NAN);
                format!("#Var.Real({})", v)
            }
            Variant::Byte(i) => {
                let v = pools.bytes.get(i as usize).cloned().unwrap_or(0);
                format!("#Var.Byte({})", v)
            }
            Variant::Short(i) => {
                let v = pools.shorts.get(i as usize).cloned().unwrap_or(0);
                format!("#Var.Short({})", v)
            }
            Variant::Integer(i) => {
                let v = pools.ints.get(i as usize).cloned().unwrap_or(0);
                format!("#Var.Integer({})", v)
            }
            Variant::Long(i) => {
                let v = pools.longs.get(i as usize).cloned().unwrap_or(0);
                format!("#Var.Long({})", v)
            }
            Variant::Unknown => "<unknown>".to_string(),
        }
    }
}

fn fmt_quoted(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for ch in s.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            _ => out.push(ch),
        }
    }
    out.push('"');
    out
}
