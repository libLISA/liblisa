use std::collections::HashMap;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) struct ConstId(u64);

impl From<u64> for ConstId {
    fn from(value: u64) -> Self {
        Self(value)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum BinOp {
    Concat = 0,
    BvShl,
    BvLShr,
    BvAShr,
    BvURem,
    BvSRem,
    BvUDiv,
    BvSDiv,
    BvRotL,
    BvRotR,
    BvSlt,
    BvSge,
    BvSgt,
    BvUgt,
    BvUlt,
    BvUle,
    BvUge,
    Eq,
    Add,
    Sub,
    Mul,
    Or,
    And,
    Xor,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum UnOp {
    BvFromInt,
    IntFromBv,
    Not,
    Extract(u32, u32),
    ZeroExt(u32),
    SignExt(u32),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Tree {
    FixedBV { val: u64, size: u32 },
    FixedInt { val: u64 },
    FixedBool { val: bool },
    BV { id: ConstId, size: u32 },
    Bool(ConstId),
    BinOp { op: BinOp, args: Box<[Tree; 2]> },
    UnOp { op: UnOp, arg: Box<Tree> },
    Ite(Box<[Tree; 3]>),
    ConstInterp,
    ForAll { bounds: Vec<Tree>, condition: Box<Tree> },
}

impl Tree {
    pub(super) fn to_bytes(&self, map: &mut HashMap<ConstId, u8>) -> Vec<u8> {
        let mut out = Vec::new();
        self.to_bytes_internal(map, &mut out);

        out
    }

    fn to_bytes_internal(&self, map: &mut HashMap<ConstId, u8>, out: &mut Vec<u8>) {
        match self {
            Tree::FixedBV {
                val,
                size,
            } => {
                out.push(0);
                out.extend(val.to_ne_bytes());
                out.extend(size.to_ne_bytes());
            },
            Tree::FixedInt {
                val,
            } => {
                out.push(1);
                out.extend(val.to_ne_bytes());
            },
            Tree::FixedBool {
                val,
            } => {
                if *val {
                    out.push(3);
                } else {
                    out.push(2);
                }
            },
            Tree::BV {
                id,
                size,
            } => {
                let n = map.len() as u8;
                let id = *map.entry(*id).or_insert(n);

                out.push(4);
                out.push(id);
                out.extend(size.to_ne_bytes());
            },
            Tree::Bool(id) => {
                let n = map.len() as u8;
                let id = *map.entry(*id).or_insert(n);

                out.push(5);
                out.push(id);
            },
            Tree::Ite(args) => {
                out.push(6);
                for arg in args.iter() {
                    arg.to_bytes_internal(map, out);
                }
            },
            Tree::ConstInterp => {
                unreachable!()
            },
            Tree::ForAll {
                bounds,
                condition,
            } => {
                out.push(7);
                out.extend(u16::try_from(bounds.len()).unwrap().to_ne_bytes());
                for bound in bounds.iter() {
                    bound.to_bytes_internal(map, out);
                }

                condition.to_bytes_internal(map, out);
            },
            Tree::UnOp {
                op: UnOp::BvFromInt,
                arg,
            } => {
                out.push(8);
                arg.to_bytes_internal(map, out);
            },
            Tree::UnOp {
                op: UnOp::Extract(hi, lo),
                arg,
            } => {
                out.push(9);
                out.extend(hi.to_ne_bytes());
                out.extend(lo.to_ne_bytes());
                arg.to_bytes_internal(map, out);
            },
            Tree::UnOp {
                op: UnOp::IntFromBv,
                arg,
            } => {
                out.push(10);
                arg.to_bytes_internal(map, out);
            },
            Tree::UnOp {
                op: UnOp::Not,
                arg,
            } => {
                out.push(11);
                arg.to_bytes_internal(map, out);
            },
            Tree::UnOp {
                op: UnOp::SignExt(num),
                arg,
            } => {
                out.push(12);
                out.extend(num.to_ne_bytes());
                arg.to_bytes_internal(map, out);
            },
            Tree::UnOp {
                op: UnOp::ZeroExt(num),
                arg,
            } => {
                out.push(13);
                out.extend(num.to_ne_bytes());
                arg.to_bytes_internal(map, out);
            },
            Tree::BinOp {
                op,
                args,
            } => {
                out.push(0x80 + (*op) as u8);
                for arg in args.iter() {
                    arg.to_bytes_internal(map, out);
                }
            },
        }
    }
}
