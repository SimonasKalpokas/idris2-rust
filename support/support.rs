#[derive(Debug, Clone)]
pub enum IdrisType {
    None,
    World,
    Int(i64),
    Char(char),
    String(String),
    Double(f64),
    Type(IdrisMetaType),
    Struct(i64, Vec<IdrisType>),
    Function(usize, Vec<IdrisType>, fn(Vec<IdrisType>) -> IdrisType),
}

#[derive(Debug, Clone)]
pub enum IdrisMetaType {
    IntType,
    StringType,
    CharType,
    DoubleType,
    WorldType,
}

pub fn idris2_apply_closure(closure: &IdrisType, arg: &IdrisType) -> IdrisType {
    match closure {
        IdrisType::Function(1, collected_args, function) => {
            let mut args = collected_args.clone();
            args.push(arg.clone());
            function(args)
        }
        IdrisType::Function(missing, collected_args, function) => {
            let mut args = collected_args.clone();
            args.push(arg.clone());
            IdrisType::Function(missing - 1, args, *function)
        }
        _ => panic!("Expected IdrisType::Function here"),
    }
}

pub fn idris2_sub_Int(args: Vec<IdrisType>) -> IdrisType {
    let a = match args.get(0).unwrap() {
        IdrisType::Int(i) => i,
        _ => panic!("unexpected value"),
    };
    let b = match args.get(1).unwrap() {
        IdrisType::Int(i) => i,
        _ => panic!("unexpected value"),
    };
    return IdrisType::Int(a - b);
}

pub fn idris2_mul_Int(args: Vec<IdrisType>) -> IdrisType {
    let a = match args.get(0).unwrap() {
        IdrisType::Int(i) => i,
        _ => panic!("unexpected value"),
    };
    let b = match args.get(1).unwrap() {
        IdrisType::Int(i) => i,
        _ => panic!("unexpected value"),
    };
    return IdrisType::Int(a * b);
}

pub fn idris2_mod_Int(args: Vec<IdrisType>) -> IdrisType {
    let a = match args.get(0).unwrap() {
        IdrisType::Int(i) => i,
        _ => panic!("unexpected value"),
    };
    let b = match args.get(1).unwrap() {
        IdrisType::Int(i) => i,
        _ => panic!("unexpected value"),
    };
    return IdrisType::Int(a % b);
}

pub fn idris2_div_Int(args: Vec<IdrisType>) -> IdrisType {
    let a = match args.get(0).unwrap() {
        IdrisType::Int(i) => i,
        _ => panic!("unexpected value"),
    };
    let b = match args.get(1).unwrap() {
        IdrisType::Int(i) => i,
        _ => panic!("unexpected value"),
    };
    return IdrisType::Int(a / b);
}

pub fn idris2_add_Int(args: Vec<IdrisType>) -> IdrisType {
    let a = match args.get(0).unwrap() {
        IdrisType::Int(i) => i,
        _ => panic!("unexpected value"),
    };
    let b = match args.get(1).unwrap() {
        IdrisType::Int(i) => i,
        _ => panic!("unexpected value"),
    };
    return IdrisType::Int(a + b);
}
pub fn idris2_mul_Double(args: Vec<IdrisType>) -> IdrisType {
    let a = match args.get(0).unwrap() {
        IdrisType::Double(i) => i,
        _ => panic!("unexpected value"),
    };
    let b = match args.get(1).unwrap() {
        IdrisType::Double(i) => i,
        _ => panic!("unexpected value"),
    };
    return IdrisType::Double(a * b);
}

pub fn strAppend(args: Vec<IdrisType>) -> IdrisType {
    let a = match args.get(0).unwrap() {
        IdrisType::String(str) => str,
        _ => panic!("unexpected value"),
    };
    let b = match args.get(1).unwrap() {
        IdrisType::String(str) => str,
        _ => panic!("unexpected value"),
    };
    return IdrisType::String(a.clone() + b);
}
pub fn idris2_gt_Int(args: Vec<IdrisType>) -> IdrisType {
    let a = match args.get(0).unwrap() {
        IdrisType::Int(i) => i,
        _ => panic!("unexpected value"),
    };
    let b = match args.get(1).unwrap() {
        IdrisType::Int(i) => i,
        _ => panic!("unexpected value"),
    };
    return IdrisType::Int(if a > b { 1 } else { 0 });
}
pub fn idris2_gte_Int(args: Vec<IdrisType>) -> IdrisType {
    let a = match args.get(0).unwrap() {
        IdrisType::Int(i) => i,
        _ => panic!("unexpected value"),
    };
    let b = match args.get(1).unwrap() {
        IdrisType::Int(i) => i,
        _ => panic!("unexpected value"),
    };
    return IdrisType::Int(if a >= b { 1 } else { 0 });
}
pub fn idris2_lte_Int(args: Vec<IdrisType>) -> IdrisType {
    let a = match args.get(0).unwrap() {
        IdrisType::Int(i) => i,
        _ => panic!("unexpected value"),
    };
    let b = match args.get(1).unwrap() {
        IdrisType::Int(i) => i,
        _ => panic!("unexpected value"),
    };
    return IdrisType::Int(if a <= b { 1 } else { 0 });
}
pub fn idris2_lt_Int(args: Vec<IdrisType>) -> IdrisType {
    let a = match args.get(0).unwrap() {
        IdrisType::Int(i) => i,
        _ => panic!("unexpected value"),
    };
    let b = match args.get(1).unwrap() {
        IdrisType::Int(i) => i,
        _ => panic!("unexpected value"),
    };
    return IdrisType::Int(if a < b { 1 } else { 0 });
}
pub fn idris2_cast_Int_to_String(args: Vec<IdrisType>) -> IdrisType {
    let a = match args.get(0).unwrap() {
        IdrisType::Int(i) => i,
        _ => panic!("unexpected value"),
    };
    return IdrisType::String(a.to_string());
}
pub fn idris2_cast_Double_to_String(args: Vec<IdrisType>) -> IdrisType {
    let a = match args.get(0).unwrap() {
        IdrisType::Double(i) => i,
        _ => panic!("unexpected value"),
    };
    return IdrisType::String(a.to_string());
}
pub fn head(args: Vec<IdrisType>) -> IdrisType {
    let a = match args.get(0).unwrap() {
        IdrisType::String(str) => str,
        _ => panic!("unexpected value"),
    };
    return IdrisType::Char(a.chars().next().unwrap());
}
pub fn idris2_eq_Int(args: Vec<IdrisType>) -> IdrisType {
    let a = match args.get(0).unwrap() {
        IdrisType::Int(i) => i,
        _ => panic!("unexpected value"),
    };
    let b = match args.get(1).unwrap() {
        IdrisType::Int(i) => i,
        _ => panic!("unexpected value"),
    };
    return IdrisType::Int(if a == b { 1 } else { 0 });
}
pub fn idris2_eq_Char(args: Vec<IdrisType>) -> IdrisType {
    let a = match args.get(0).unwrap() {
        IdrisType::Char(i) => i,
        _ => panic!("unexpected value"),
    };
    let b = match args.get(1).unwrap() {
        IdrisType::Char(i) => i,
        _ => panic!("unexpected value"),
    };
    return IdrisType::Int(if a == b { 1 } else { 0 });
}

pub fn idris2_crash(args: Vec<IdrisType>) -> IdrisType {
    let a = match args.get(0).unwrap() {
        IdrisType::String(str) => str,
        _ => panic!("unexpected value"),
    };
    panic!("{a}");
}

pub fn Prelude_IO_prim__putStr(args: Vec<IdrisType>) -> IdrisType {
    let val_v0 = args.get(0).unwrap().clone();
    match val_v0 {
        IdrisType::String(ref str) => print!("{}", str),
        _ => panic!("Unexpected type"),
    };
    return IdrisType::None;
}
