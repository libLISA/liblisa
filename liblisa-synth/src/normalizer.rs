use std::mem::swap;

use arrayvec::ArrayVec;
use liblisa::semantics::default::computation::{Arg, ArgEncoding, AsComputationRef, OutputEncoding, SynthesizedComputation};
use liblisa::semantics::default::ops::Op;
use liblisa::semantics::default::Expression;
use liblisa::semantics::{Computation, IoType, ARG_NAMES};
use liblisa::utils::{bitmask_u128, deposit_bits_u128, sign_extend, switch_endianness_u128};
use liblisa::value::OwnedValue;
use log::{debug, info, trace};

#[derive(Clone, PartialEq)]
enum Node {
    Arg {
        index: usize,
        num_bits: usize,
        encoding: ArgEncoding,
    },
    Const(i128),
    Op {
        op: Op,
        args: Vec<Node>,
    },
}

#[derive(Default)]
struct ArgumentUse(Vec<u128>);

impl ArgumentUse {
    pub fn arg(index: usize, mask: u128) -> Self {
        let mut v = vec![0; index + 1];
        v[index] = mask;

        Self(v)
    }

    pub fn union_with(&mut self, other: &ArgumentUse) {
        if other.0.len() > self.0.len() {
            self.0.resize(other.0.len(), 0);
        }

        for (lhs, rhs) in self.0.iter_mut().zip(other.0.iter()) {
            *lhs |= *rhs;
        }
    }

    pub fn single_arg(&self) -> Option<(usize, u128)> {
        if self.0.iter().filter(|&&v| v != 0).count() == 1 {
            let (index, mask) = self.0.iter().enumerate().find(|&(_, &v)| v != 0).unwrap();

            Some((index, *mask))
        } else {
            None
        }
    }
}

impl std::fmt::Debug for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Arg {
                index, ..
            } => write!(f, "{}", ARG_NAMES[*index]),
            Self::Const(c) => write!(f, "0x{c:X}"),
            Self::Op {
                op,
                args,
            } => {
                write!(f, "{op:?}{args:?}")
            },
        }
    }
}

const ALL_BITS: usize = 128;

impl Node {
    pub fn as_const(&self) -> Option<i128> {
        match self {
            Node::Const(c) => Some(*c),
            _ => None,
        }
    }

    pub fn as_op_args_mut(&mut self, matching_op: Op) -> Option<&mut Vec<Node>> {
        if let Node::Op {
            op,
            args,
        } = self
        {
            if op == &matching_op {
                return Some(args)
            }
        }

        None
    }

    pub fn num_nodes(&self) -> usize {
        1 + if let Node::Op {
            args, ..
        } = self
        {
            args.iter().map(|arg| arg.num_nodes()).sum::<usize>()
        } else {
            0
        }
    }

    fn get_arg_num_bits(&self, arg_index: usize) -> Option<usize> {
        match self {
            Node::Arg {
                index,
                num_bits,
                ..
            } => {
                if *index == arg_index {
                    Some(*num_bits)
                } else {
                    None
                }
            },
            Node::Const(_) => None,
            Node::Op {
                args, ..
            } => args
                .iter()
                .map(|arg| arg.get_arg_num_bits(arg_index))
                .reduce(|lhs, rhs| match (lhs, rhs) {
                    (None, None) => None,
                    (None, Some(val)) | (Some(val), None) => Some(val),
                    (Some(lhs), Some(rhs)) => {
                        if lhs == rhs {
                            Some(lhs)
                        } else {
                            panic!("Tree contains argument uses with different num_bits: {self:?}")
                        }
                    },
                })
                .unwrap(),
        }
    }

    fn is_arg_encoding_used(&self, arg_index: usize, wanted_encoding: ArgEncoding) -> bool {
        match self {
            Node::Arg {
                index,
                encoding,
                ..
            } => {
                if *index == arg_index {
                    *encoding == wanted_encoding
                } else {
                    false
                }
            },
            Node::Const(_) => false,
            Node::Op {
                args, ..
            } => args.iter().any(|arg| arg.is_arg_encoding_used(arg_index, wanted_encoding)),
        }
    }

    fn interpret_u128(encoding: &ArgEncoding, n: u128, num_bits: usize) -> i128 {
        let n = match encoding {
            ArgEncoding::SignedLittleEndian | ArgEncoding::UnsignedLittleEndian => switch_endianness_u128(n, num_bits),
            ArgEncoding::SignedBigEndian | ArgEncoding::UnsignedBigEndian => n,
        };

        match encoding {
            ArgEncoding::SignedLittleEndian | ArgEncoding::SignedBigEndian => sign_extend(n as i128, num_bits),
            ArgEncoding::UnsignedLittleEndian | ArgEncoding::UnsignedBigEndian => n as i128,
        }
    }

    pub fn eval_with(&self, get_arg: &impl Fn(usize) -> i128) -> i128 {
        match self {
            Node::Arg {
                index,
                num_bits,
                encoding,
            } => Self::interpret_u128(encoding, get_arg(*index) as u128, *num_bits),
            Node::Const(c) => *c,
            Node::Op {
                op,
                args,
            } => {
                let mut vals = args.iter().map(|arg| arg.eval_with(get_arg)).collect::<ArrayVec<_, 4>>();
                op.eval_from_stack(&|_| unreachable!(), vals.pop().unwrap_or_default(), &mut vals)
            },
        }
    }

    pub fn num_bits(&self) -> usize {
        match self {
            Node::Arg {
                num_bits,
                encoding,
                ..
            } => match encoding {
                ArgEncoding::SignedLittleEndian | ArgEncoding::SignedBigEndian => 128,
                ArgEncoding::UnsignedBigEndian => *num_bits,
                ArgEncoding::UnsignedLittleEndian => (*num_bits + 7) / 8 * 8,
            },
            Node::Const(c) => (128 - c.leading_zeros()) as usize,
            Node::Op {
                op,
                args,
            } => {
                let arg_bits = args.iter().map(|arg| arg.num_bits()).collect::<Vec<_>>();
                let arg_max = arg_bits.iter().copied().max().unwrap_or(0);
                match op {
                    Op::Hole(_) | Op::Const(_) => unreachable!(),
                    Op::Not => ALL_BITS,
                    Op::Crop {
                        num_bits,
                    } => *num_bits as usize,
                    Op::SignExtend {
                        ..
                    } => ALL_BITS,
                    Op::Select {
                        num_take, ..
                    } => *num_take as usize,
                    Op::Parity => 1,
                    Op::IsZero => 1,
                    Op::ByteMask => arg_max / 8,
                    Op::TrailingZeros | Op::LeadingZeros | Op::PopCount => 8,
                    Op::Add => arg_max + 1,
                    Op::Sub => ALL_BITS,
                    Op::Mul | Op::CarrylessMul => arg_bits.iter().copied().reduce(|a, b| a + b).unwrap().min(ALL_BITS),
                    Op::Div => arg_max,
                    Op::UnsignedDiv => arg_max,
                    Op::Rem => arg_bits[1],
                    Op::UnsignedRem => arg_bits[1],
                    Op::Shl => ALL_BITS,
                    Op::Shr => arg_bits[0],
                    Op::And => arg_bits.iter().copied().reduce(|a, b| a.min(b)).unwrap().min(ALL_BITS),
                    Op::Or => arg_max,
                    Op::Xor => arg_max,
                    Op::CmpLt => 1,
                    Op::Rol {
                        num_bits,
                    } => *num_bits as usize,
                    Op::IfZero => *arg_bits.iter().skip(1).max().unwrap(),
                    Op::SwapBytes {
                        num_bits,
                    } => ((*num_bits as usize + 7) / 8) * 8,
                    Op::BitMask => ALL_BITS,
                    Op::DepositBits => arg_bits[1],
                    Op::ExtractBits => arg_bits[0].min(arg_bits[1]),
                }
            },
        }
    }

    fn child_bits_needed(op: Op, bits_needed: u128) -> u128 {
        let max_bits_needed = 128 - bits_needed.leading_zeros() as usize;
        match op {
            Op::Hole(_) | Op::Const(_) => unreachable!(),
            Op::Crop {
                num_bits,
            }
            | Op::SignExtend {
                num_bits,
            }
            | Op::SwapBytes {
                num_bits,
            } => bits_needed & bitmask_u128(num_bits as u32),
            Op::Select {
                num_skip,
                num_take,
            } => {
                if num_skip >= 128 {
                    0
                } else {
                    (bits_needed & bitmask_u128(num_take as u32)) << num_skip
                }
            },
            Op::Rol {
                ..
            } => unreachable!(),
            Op::Not | Op::And | Op::Or | Op::Xor => bits_needed,
            Op::Add => bitmask_u128(max_bits_needed as u32),
            Op::ByteMask => u128::MAX, // TODO
            Op::Parity
            | Op::IsZero
            | Op::TrailingZeros
            | Op::LeadingZeros
            | Op::PopCount
            | Op::Sub
            | Op::Mul
            | Op::CarrylessMul
            | Op::Div
            | Op::UnsignedDiv
            | Op::Rem
            | Op::UnsignedRem
            | Op::CmpLt
            | Op::BitMask => u128::MAX,
            Op::DepositBits | Op::ExtractBits => u128::MAX,
            Op::Shl | Op::Shr | Op::IfZero => unreachable!(),
        }
    }

    /// max_bits_needed: we're going to throw away bits above this threshold, so they can be anything.
    pub fn reduce(&mut self, bits_needed: u128) -> ArgumentUse {
        if bits_needed == 0 {
            *self = Node::Const(0);
            ArgumentUse::default()
        } else {
            match self {
                Node::Op {
                    op,
                    args,
                } => {
                    let argument_use = match op {
                        Op::IfZero => {
                            let mut u = args[0].reduce(u128::MAX);
                            u.union_with(&args[1].reduce(bits_needed));
                            u.union_with(&args[2].reduce(bits_needed));
                            u
                        },
                        Op::Rol {
                            num_bits,
                        } => {
                            let mut u = args[0].reduce(bitmask_u128(*num_bits as u32));
                            // TODO: Determine the number of bits needed based on the size of the operation; Crop the rotate amount in the Op.
                            u.union_with(&args[1].reduce(u128::MAX));
                            u
                        },
                        Op::Shl | Op::Shr => {
                            let num_shift_bits = args[1].num_bits().min(7);
                            let value_mask = (0..1 << num_shift_bits)
                                .map(|shift_val| match op {
                                    Op::Shl => bits_needed >> shift_val,
                                    Op::Shr => bits_needed << shift_val,
                                    _ => unreachable!(),
                                })
                                .reduce(|a, b| a | b)
                                .unwrap();

                            let mut u = args[0].reduce(value_mask);
                            u.union_with(&args[1].reduce(0x7f));
                            u
                        },
                        _ => {
                            let child_max_bits_needed = Self::child_bits_needed(*op, bits_needed);
                            let mut u = ArgumentUse::default();
                            for arg in args.iter_mut() {
                                u.union_with(&arg.reduce(child_max_bits_needed));
                            }

                            u
                        },
                    };

                    self.reduce_internal(bits_needed, &argument_use);

                    argument_use
                },
                Node::Const(val) => {
                    *val &= bits_needed as i128;
                    ArgumentUse::default()
                },
                Node::Arg {
                    index,
                    num_bits,
                    encoding,
                } => {
                    let mask = match encoding {
                        ArgEncoding::SignedBigEndian | ArgEncoding::UnsignedBigEndian => {
                            bits_needed & bitmask_u128(*num_bits as u32)
                        },
                        ArgEncoding::SignedLittleEndian | ArgEncoding::UnsignedLittleEndian => {
                            // TODO: Verify that this is correct!
                            switch_endianness_u128(bits_needed, *num_bits) & bitmask_u128(*num_bits as u32)
                        },
                    };
                    ArgumentUse::arg(*index, mask)
                },
            }
        }
    }

    fn reduce_internal(&mut self, bits_needed: u128, argument_use: &ArgumentUse) {
        if bits_needed.is_power_of_two()
            && let Some((arg_index, arg_bits)) = argument_use.single_arg()
            && arg_bits.count_ones() < 8
            && self.num_nodes() > 7
        {
            let num_bits = self.get_arg_num_bits(arg_index).unwrap();
            let (encoding, swap) = if self.is_arg_encoding_used(arg_index, ArgEncoding::UnsignedBigEndian) {
                (ArgEncoding::UnsignedBigEndian, false)
            } else if self.is_arg_encoding_used(arg_index, ArgEncoding::SignedBigEndian) {
                (ArgEncoding::SignedBigEndian, false)
            } else if self.is_arg_encoding_used(arg_index, ArgEncoding::UnsignedLittleEndian) {
                (ArgEncoding::UnsignedLittleEndian, true)
            } else if self.is_arg_encoding_used(arg_index, ArgEncoding::SignedLittleEndian) {
                (ArgEncoding::SignedLittleEndian, true)
            } else {
                unreachable!()
            };

            trace!("Bits used for arg {arg_index}: {arg_bits:X}");

            let valid_values = (0..128)
                .filter(|&x| {
                    let n = deposit_bits_u128(x as u128, arg_bits) as i128;

                    // let n = if preswap {
                    //     switch_endianness_u128(n as u128, num_bits) as i128
                    // } else {
                    //     n
                    // };

                    let result = self.eval_with(&|index| {
                        // TODO: If we don't use any bits of one of the values this might be valid...
                        assert_eq!(arg_index, index, "Discovered a new argument in: {self:?}");
                        n
                    }) as u128
                        & bits_needed
                        != 0;

                    trace!("Evaluating {x} with value {n:X} = {result}");

                    result
                })
                .fold(0u128, |acc, el| acc | (1 << (127 - el)));
            trace!("Valid values: {valid_values:X?}");

            let extra_rotate = 128 - valid_values.trailing_zeros();
            trace!("Extra rotate: {extra_rotate}");
            let valid_values = valid_values.rotate_left(extra_rotate);
            trace!("Valid values: {valid_values:X?}");

            let proposed_solution = Node::Op {
                op: Op::Shl,
                args: vec![
                    Node::Op {
                        op: Op::Select {
                            num_skip: (extra_rotate.wrapping_sub(1) & 0x7f) as u8,
                            num_take: 1,
                        },
                        args: vec![Node::Op {
                            op: Op::Shl,
                            args: vec![
                                Node::Const(valid_values as i128),
                                Node::Op {
                                    op: Op::ExtractBits,
                                    args: vec![
                                        Node::Arg {
                                            index: arg_index,
                                            num_bits,
                                            encoding,
                                        },
                                        Node::Const(if swap {
                                            switch_endianness_u128(arg_bits, num_bits) as i128
                                        } else {
                                            arg_bits as i128
                                        }),
                                    ],
                                },
                            ],
                        }],
                    },
                    Node::Const(bits_needed.trailing_zeros() as i128),
                ],
            };

            trace!("Proposed solution: {proposed_solution:?}");

            *self = proposed_solution;
        }

        let (op, args) = if let Node::Op {
            op,
            args,
        } = self
        {
            (op, args)
        } else {
            unreachable!()
        };

        let max_bits_needed = 128 - bits_needed.leading_zeros() as usize;

        debug!("reduce({op:?} with args {args:?}, max_bits_needed={max_bits_needed}, bits_needed={bits_needed:X})");
        match op {
            Op::Hole(_) | Op::Const(_) => unreachable!(),
            Op::Shl | Op::Shr => {
                if args[1].as_const() == Some(0) {
                    *self = args.remove(0);
                } else if op == &Op::Shr {
                    if let Some(c) = args[1].as_const() {
                        if c >= 0 && c <= ALL_BITS as i128 && max_bits_needed <= ALL_BITS - c as usize {
                            trace!("Reducing shr -> select");
                            args.remove(1);
                            *op = Op::Select {
                                num_skip: c.try_into().unwrap(),
                                num_take: max_bits_needed.try_into().unwrap(),
                            };
                        }
                    }
                }
            },
            Op::And => {
                let left_mask = mask(args[0].num_bits());
                let right_mask = mask(args[1].num_bits());
                trace!("left_mask={left_mask:X}, right_mask={right_mask:X}");
                if args[0].as_const().map(|x| x & right_mask == 0).unwrap_or(false)
                    || args[1].as_const().map(|x| x & left_mask == 0).unwrap_or(false)
                {
                    trace!("Reducing AND of {args:?} to 0");
                    *self = Node::Const(0);
                } else if args[0].as_const().map(|x| x & right_mask == right_mask).unwrap_or(false) {
                    trace!("Reducing AND of {args:?} to second operand");
                    *self = args.remove(1);
                } else if args[1].as_const().map(|x| x & left_mask == left_mask).unwrap_or(false) {
                    trace!("Reducing AND of {args:?} to first operand");
                    *self = args.remove(0);
                } else if args[0]
                    .as_const()
                    .map(|x| x.trailing_ones() + x.leading_zeros() == 128)
                    .unwrap_or(false)
                {
                    *self = Node::Op {
                        op: Op::Crop {
                            num_bits: args[0].as_const().unwrap().trailing_ones() as u8,
                        },
                        args: vec![args.remove(1)],
                    };
                } else if args[1]
                    .as_const()
                    .map(|x| x.trailing_ones() + x.leading_zeros() == 128)
                    .unwrap_or(false)
                {
                    *self = Node::Op {
                        op: Op::Crop {
                            num_bits: args[1].as_const().unwrap().trailing_ones() as u8,
                        },
                        args: vec![args.remove(0)],
                    };
                } else if let Node::Op {
                    op: Op::Crop {
                        num_bits,
                    },
                    args: lhs_args,
                } = &mut args[0]
                {
                    *self = Node::Op {
                        op: Op::Crop {
                            num_bits: *num_bits,
                        },
                        args: vec![Node::Op {
                            op: Op::And,
                            args: vec![lhs_args.remove(0), args.remove(1)],
                        }],
                    };
                } else if let Node::Op {
                    op: Op::Crop {
                        num_bits,
                    },
                    args: rhs_args,
                } = &mut args[1]
                {
                    let rhs = rhs_args.remove(0);
                    *self = Node::Op {
                        op: Op::Crop {
                            num_bits: *num_bits,
                        },
                        args: vec![Node::Op {
                            op: Op::And,
                            args: vec![args.remove(0), rhs],
                        }],
                    };
                }
            },
            Op::Or => {
                let left_mask = mask(args[0].num_bits());
                let right_mask = mask(args[1].num_bits());
                let combined_mask = left_mask | right_mask;
                trace!("left_mask={left_mask:X}, right_mask={right_mask:X}");
                if args[0].as_const().map(|x| x & combined_mask == 0).unwrap_or(false) {
                    trace!("Reducing OR of {args:?} to first operand");
                    *self = args.remove(1);
                } else if args[1].as_const().map(|x| x & combined_mask == 0).unwrap_or(false) {
                    trace!("Reducing OR of {args:?} to second operand");
                    *self = args.remove(0);
                } else if args[0]
                    .as_const()
                    .map(|x| x & combined_mask == combined_mask)
                    .unwrap_or(false)
                {
                    trace!("Reducing OR of {args:?} to -1");
                    *self = Node::Const(-1);
                } else if args[1]
                    .as_const()
                    .map(|x| x & combined_mask == combined_mask)
                    .unwrap_or(false)
                {
                    trace!("Reducing OR of {args:?} to -1");
                    *self = Node::Const(-1);
                }
            },
            Op::Xor => {
                if args[0].as_const().map(|x| x as u128 & bits_needed == 0).unwrap_or(false) {
                    trace!("Reducing XOR of {args:?} to first operand");
                    *self = args.remove(1);
                } else if args[1].as_const().map(|x| x as u128 & bits_needed == 0).unwrap_or(false) {
                    trace!("Reducing XOR of {args:?} to second operand");
                    *self = args.remove(0);
                }
            },
            Op::Crop {
                num_bits,
            } => {
                if args[0].num_bits() <= *num_bits as usize || *num_bits as usize >= max_bits_needed {
                    trace!(
                        "Eliminating crop[{num_bits}] of {args:?} (returning {} bits), because it's not needed (max_bits_needed={max_bits_needed})",
                        args[0].num_bits()
                    );
                    *self = args.remove(0);
                } else if let Node::Op {
                    op: Op::Select {
                        num_skip,
                        num_take,
                    },
                    args: inner_args,
                } = &mut args[0]
                {
                    *op = Op::Select {
                        num_skip: *num_skip,
                        num_take: *num_take.min(num_bits),
                    };

                    args[0] = inner_args.remove(0);
                }
                //  else {
                //     *num_bits = (*num_bits).min(max_bits_needed.try_into().unwrap());

                //     // if let Some(args) = args[0].as_op_args(Op::Not) {
                //     //     if let Some(args) = args[0].as_op_args(Op::IsZero) {
                //     //         if let Some(args) = args[0].as_op_args(Op::Crop { num_bits: 1 }) {

                //     //         }
                //     //     }
                //     // }
                // }
            },
            Op::Select {
                num_skip,
                num_take,
            } => {
                if *num_skip == 0 {
                    *self = Node::Op {
                        op: Op::Crop {
                            num_bits: *num_take,
                        },
                        args: vec![args.remove(0)],
                    }
                } else if let Node::Op {
                    op:
                        Op::Select {
                            num_skip: inner_num_skip,
                            num_take: inner_num_take,
                        },
                    args: inner_args,
                } = &args[0]
                {
                    *self = Node::Op {
                        op: Op::Select {
                            num_skip: *num_skip + *inner_num_skip,
                            num_take: (*num_take).min(inner_num_take.saturating_sub(*num_skip)),
                        },
                        args: inner_args.clone(),
                    }
                } else if *num_take == 1
                    && let Node::Op {
                        op: Op::Shr,
                        args: inner_args,
                    } = &args[0]
                    && let Some(c) = inner_args[0].as_const()
                    && c >= 0
                {
                    trace!("Shift with constant {c:X}");
                    let valid_values = (0..128)
                        .filter(|shift| (c >> shift) & 1 != 0)
                        .fold(0i128, |acc, el| acc | (1 << (127 - el)));
                    trace!("Valid values: {valid_values:X?}");
                    let valid_values = valid_values.rotate_left(*num_skip as u32);
                    trace!("Valid values: {valid_values:X?}");

                    let extra_rotate = 128 - valid_values.trailing_zeros();
                    trace!("Extra rotate: {extra_rotate}");
                    let valid_values = valid_values.rotate_left(extra_rotate);
                    trace!("Valid values: {valid_values:X?}");

                    let shift = inner_args[1].clone();
                    args[0] = Node::Op {
                        op: Op::Shl,
                        args: vec![Node::Const(valid_values), shift],
                    };
                    *num_skip = (extra_rotate - 1) as u8;
                } else if *num_take == 1
                    && let Node::Op {
                        op: Op::Shl,
                        args: inner_args,
                    } = &mut args[0]
                    && let Some(c) = inner_args[0].as_const()
                    && c >= 0
                    && c.trailing_zeros() > 0
                {
                    trace!("Shift with constant: {c:X} << x");

                    let trailing = c.trailing_zeros();
                    trace!("Trailing: {trailing}");

                    let remove = trailing.min(*num_skip as u32);
                    *num_skip -= remove as u8;
                    inner_args[0] = Node::Const(c >> remove);
                } else if let Node::Op {
                    op: Op::Shl,
                    args: inner_args,
                } = &mut args[0]
                    && let Some(c) = inner_args[1].as_const()
                {
                    if c > *num_skip as i128 {
                        *num_skip = 0;
                        inner_args[1] = Node::Const(c - *num_skip as i128);
                    } else {
                        *num_skip -= c as u8;
                        inner_args[1] = Node::Const(0);
                    }
                } else if let Some(num_left_to_take) = args[0].num_bits().checked_sub(*num_skip as usize) {
                    *num_take = (*num_take).min(num_left_to_take.try_into().unwrap());
                } else {
                    trace!("Eliminating select because select is selecting bits that are always zero");
                    *self = Node::Const(0);
                }
            },
            Op::SignExtend {
                num_bits,
            } => {
                if *num_bits as usize > args[0].num_bits() {
                    *self = args.remove(0);
                }
            },
            Op::IfZero => {
                let (condition, rest) = args.split_at_mut(1);
                let (if_zero, if_nonzero) = rest.split_at_mut(1);
                let (condition, if_zero, if_nonzero) = (&mut condition[0], &mut if_zero[0], &mut if_nonzero[0]);
                if let Some(val) = condition.as_const() {
                    if val == 0 {
                        *self = args.remove(1);
                    } else {
                        *self = args.remove(2);
                    }
                } else if *if_zero == *if_nonzero {
                    *self = args.remove(1);
                } else if if_zero.as_const() == Some(0) && if_nonzero.as_const() == Some(1) {
                    *self = Node::Op {
                        op: Op::Crop {
                            num_bits: 1,
                        },
                        args: vec![Node::Op {
                            op: Op::Not,
                            args: vec![Node::Op {
                                op: Op::IsZero,
                                args: vec![args.remove(0)],
                            }],
                        }],
                    };
                } else if if_zero.as_const() == Some(1) && if_nonzero.as_const() == Some(0) {
                    *op = Op::IsZero;
                    args.drain(1..).for_each(drop);
                } else if max_bits_needed == 1 && condition.num_bits() == 1 && if_nonzero.as_const() == Some(1) {
                    // if x = 0 then b else 1 fi == x | b
                    *self = Node::Op {
                        op: Op::Or,
                        args: vec![args.remove(0), args.remove(0)],
                    };
                } else if max_bits_needed == 1 && condition.num_bits() == 1 && if_zero.as_const() == Some(1) {
                    // if x = 0 then 1 else b fi == not(x) | b
                    *self = Node::Op {
                        op: Op::Or,
                        args: vec![
                            Node::Op {
                                op: Op::Crop {
                                    num_bits: 1,
                                },
                                args: vec![Node::Op {
                                    op: Op::Not,
                                    args: vec![args.remove(0)],
                                }],
                            },
                            args.remove(1),
                        ],
                    };
                } else if max_bits_needed == 1 && condition.num_bits() == 1 && if_nonzero.as_const() == Some(0) {
                    // if x = 0 then b else 0 fi == not(x) & b
                    *self = Node::Op {
                        op: Op::And,
                        args: vec![
                            Node::Op {
                                op: Op::Crop {
                                    num_bits: 1,
                                },
                                args: vec![Node::Op {
                                    op: Op::Not,
                                    args: vec![args.remove(0)],
                                }],
                            },
                            args.remove(0),
                        ],
                    };
                } else if max_bits_needed == 1 && condition.num_bits() == 1 && if_zero.as_const() == Some(0) {
                    // if x = 0 then 0 else b fi == x & b
                    *self = Node::Op {
                        op: Op::And,
                        args: vec![args.remove(0), args.remove(1)],
                    };
                } else if let Node::Op {
                    op: Op::Crop {
                        num_bits: 1,
                    },
                    args,
                } = condition
                    && let Node::Op {
                        op: Op::Not,
                        args: not_args,
                    } = &mut args[0]
                {
                    swap(if_zero, if_nonzero);
                    args[0] = not_args.remove(0);
                } else if let Node::Op {
                    op: Op::Select {
                        num_take: 1, ..
                    },
                    args,
                } = condition
                    && let Node::Op {
                        op: Op::Not,
                        args: not_args,
                    } = &mut args[0]
                {
                    swap(if_zero, if_nonzero);
                    args[0] = not_args.remove(0);
                } else if let Node::Op {
                    op: Op::IsZero,
                    args,
                } = condition
                {
                    swap(if_zero, if_nonzero);
                    *condition = args.remove(0);
                } else if let Node::Op {
                    op: Op::IfZero,
                    args: inner_args,
                } = if_zero
                    && inner_args[1] == *if_nonzero
                {
                    // IfZero(C1, IfZero(C2, X, Y), X)
                    // => X if C1 != 0 | C2 == 0 otherwise Y
                    // => X if IsZero(C1 == 0 & C2 != 0) otherwise Y
                    // => IfZero(C1 & !C2, X, Y)
                    let condition = condition.clone();
                    let inner_condition = inner_args[0].clone();
                    let common_result = if_nonzero.clone();
                    let inner_result = inner_args[2].clone();
                    args[0] = Node::Op {
                        op: Op::And,
                        args: vec![
                            Node::Op {
                                op: Op::IsZero,
                                args: vec![condition],
                            },
                            Node::Op {
                                op: Op::Not,
                                args: vec![Node::Op {
                                    op: Op::IsZero,
                                    args: vec![inner_condition],
                                }],
                            },
                        ],
                    };
                    args[1] = common_result;
                    args[2] = inner_result;
                } else if let Node::Op {
                    op: Op::IfZero,
                    args: inner_args,
                } = if_zero
                    && inner_args[2] == *if_nonzero
                {
                    // IfZero(C1, IfZero(C2, Y, X), X)
                    // => X if C1 != 0 | C2 != 0 otherwise Y
                    // => X if IsZero(C1 == 0 & C2 == 0) otherwise Y
                    // => IfZero(C1 & C2, X, Y)
                    let condition = condition.clone();
                    let inner_condition = inner_args[0].clone();
                    let common_result = if_nonzero.clone();
                    let inner_result = inner_args[1].clone();
                    args[0] = Node::Op {
                        op: Op::And,
                        args: vec![
                            Node::Op {
                                op: Op::IsZero,
                                args: vec![condition],
                            },
                            Node::Op {
                                op: Op::IsZero,
                                args: vec![inner_condition],
                            },
                        ],
                    };
                    args[1] = common_result;
                    args[2] = inner_result;
                } else if let Node::Op {
                    op: Op::IfZero,
                    args: inner_args,
                } = if_nonzero
                    && inner_args[1] == *if_zero
                {
                    // IfZero(C1, Y, IfZero(C2, Y, X))
                    // => Y if C1 == 0 | C2 == 0 otherwise X
                    // => Y if IsZero(C1 != 0 & C2 != 0) otherwise X
                    // => IfZero(C1 | C2, Y, X)
                    let condition = condition.clone();
                    let inner_condition = inner_args[0].clone();
                    let common_result = if_zero.clone();
                    let inner_result = inner_args[2].clone();
                    args[0] = Node::Op {
                        op: Op::Or,
                        args: vec![
                            Node::Op {
                                op: Op::IsZero,
                                args: vec![condition],
                            },
                            Node::Op {
                                op: Op::IsZero,
                                args: vec![inner_condition],
                            },
                        ],
                    };
                    args[1] = inner_result;
                    args[2] = common_result;
                } else if let Node::Op {
                    op: Op::IfZero,
                    args: inner_args,
                } = if_nonzero
                    && inner_args[2] == *if_zero
                {
                    // IfZero(C1, Y, IfZero(C2, X, Y))
                    // => X if C1 != 0 & C2 == 0 otherwise Y
                    // => IfZero(!C1 & C2, X, Y)
                    let condition = condition.clone();
                    let inner_condition = inner_args[0].clone();
                    let common_result = if_zero.clone();
                    let inner_result = inner_args[1].clone();
                    args[0] = Node::Op {
                        op: Op::And,
                        args: vec![
                            Node::Op {
                                op: Op::Not,
                                args: vec![Node::Op {
                                    op: Op::IsZero,
                                    args: vec![condition],
                                }],
                            },
                            Node::Op {
                                op: Op::IsZero,
                                args: vec![inner_condition],
                            },
                        ],
                    };
                    args[1] = common_result;
                    args[2] = inner_result;
                }
            },
            Op::IsZero => {
                if let Node::Op {
                    op: Op::Sub,
                    args: sub_args,
                } = &mut args[0]
                    && sub_args[0].num_bits() == 1
                    && sub_args[1].as_const() == Some(1)
                {
                    *self = Node::Op {
                        op: Op::Crop {
                            num_bits: 1,
                        },
                        args: vec![sub_args.remove(0)],
                    };
                } else if args[0].num_bits() == 1 {
                    trace!("Reducing IsZero of 1-bit value {:?} to Crop[1](Not(..))", args[0]);
                    *self = Node::Op {
                        op: Op::Crop {
                            num_bits: 1,
                        },
                        args: vec![Node::Op {
                            op: Op::Not,
                            args: vec![args.remove(0)],
                        }],
                    };
                }
            },
            Op::Not => {
                if let Some(args) = args[0].as_op_args_mut(Op::Not) {
                    trace!("Eliminating double not");
                    *self = args.remove(0);
                } else if let Node::Op {
                    op: Op::And,
                    args,
                } = &mut args[0]
                {
                    if args.iter().any(|a| a.op() == Some(Op::Not)) {
                        // Not(A & B) = Not(A) | Not(B)
                        *self = Node::Op {
                            op: Op::Or,
                            args: args
                                .drain(..)
                                .map(|arg| Node::Op {
                                    op: Op::Not,
                                    args: vec![arg],
                                })
                                .collect(),
                        };
                    }
                } else if let Node::Op {
                    op: Op::Or,
                    args,
                } = &mut args[0]
                {
                    if args.iter().any(|a| a.op() == Some(Op::Not)) {
                        // Not(A | B) = Not(A) & Not(B)
                        *self = Node::Op {
                            op: Op::And,
                            args: args
                                .drain(..)
                                .map(|arg| Node::Op {
                                    op: Op::Not,
                                    args: vec![arg],
                                })
                                .collect(),
                        };
                    }
                }
            },
            Op::Add => {
                if max_bits_needed == 1 && args[1].as_const() == Some(1) {
                    *self = Node::Op {
                        op: Op::Not,
                        args: vec![args.remove(0)],
                    };
                } else if max_bits_needed == 1 && args[0].as_const() == Some(1) {
                    *self = Node::Op {
                        op: Op::Not,
                        args: vec![args.remove(1)],
                    };
                } else if args[0].as_const() == Some(0) {
                    trace!("Eliminating add with 0 on lhs");
                    *self = args.remove(1);
                } else if args[1].as_const() == Some(0) {
                    trace!("Eliminating add with 0 on rhs");
                    *self = args.remove(0);
                } else if let Some(c) = args[0].as_const()
                    && c < 0
                    && let Some(c_neg) = c.checked_neg()
                {
                    *self = Node::Op {
                        op: Op::Sub,
                        args: vec![args.remove(1), Node::Const(c_neg)],
                    }
                } else if let Some(c) = args[1].as_const()
                    && c < 0
                    && let Some(c_neg) = c.checked_neg()
                {
                    *self = Node::Op {
                        op: Op::Sub,
                        args: vec![args.remove(0), Node::Const(c_neg)],
                    }
                } else if let Node::Op {
                    op: inner_op @ (Op::Add | Op::Sub),
                    args: inner_args,
                } = &args[0]
                    && let Some(c1) = args[1].as_const()
                    && let Some(c2) = inner_args[0].as_const()
                {
                    *self = Node::Op {
                        op: *inner_op,
                        args: vec![Node::Const(c2.wrapping_add(c1)), inner_args[1].clone()],
                    }
                } else if let Node::Op {
                    op: inner_op @ (Op::Add | Op::Sub),
                    args: inner_args,
                } = &args[0]
                    && let Some(c1) = args[1].as_const()
                    && let Some(c2) = inner_args[1].as_const()
                {
                    *self = Node::Op {
                        op: *inner_op,
                        args: vec![
                            inner_args[0].clone(),
                            Node::Const(if *inner_op == Op::Add {
                                c2.wrapping_add(c1)
                            } else {
                                c2.wrapping_sub(c1)
                            }),
                        ],
                    }
                } else if let Node::Op {
                    op: inner_op @ (Op::Add | Op::Sub),
                    args: inner_args,
                } = &args[1]
                    && let Some(c1) = args[0].as_const()
                    && let Some(c2) = inner_args[0].as_const()
                {
                    *self = Node::Op {
                        op: *inner_op,
                        args: vec![Node::Const(c2.wrapping_add(c1)), inner_args[1].clone()],
                    }
                } else if let Node::Op {
                    op: inner_op @ (Op::Add | Op::Sub),
                    args: inner_args,
                } = &args[1]
                    && let Some(c1) = args[0].as_const()
                    && let Some(c2) = inner_args[1].as_const()
                {
                    *self = Node::Op {
                        op: *inner_op,
                        args: vec![
                            inner_args[0].clone(),
                            Node::Const(if *inner_op == Op::Add {
                                c2.wrapping_add(c1)
                            } else {
                                c2.wrapping_sub(c1)
                            }),
                        ],
                    }
                } else if let Node::Op {
                    op: Op::Shl,
                    args: inner_args,
                } = &args[1]
                    && let Some(c) = inner_args[1].as_const()
                    && c > 0
                    && c < 128
                    && args[0].num_bits() <= c as usize
                {
                    *op = Op::Or;
                } else if let Node::Op {
                    op: Op::Shl,
                    args: inner_args,
                } = &args[0]
                    && let Some(c) = inner_args[1].as_const()
                    && c > 0
                    && c < 128
                    && args[1].num_bits() <= c as usize
                {
                    *op = Op::Or;
                }
            },
            Op::Sub => {
                if max_bits_needed == 1 && args[1].as_const() == Some(1) {
                    *self = Node::Op {
                        op: Op::Not,
                        args: vec![args.remove(0)],
                    };
                } else if args[1].as_const() == Some(0) {
                    trace!("Eliminating sub with 0 on rhs");
                    *self = args.remove(0);
                } else if let Some(c) = args[1].as_const()
                    && c < 0
                    && let Some(c_neg) = c.checked_neg()
                {
                    *self = Node::Op {
                        op: Op::Add,
                        args: vec![args.remove(0), Node::Const(c_neg)],
                    }
                } else if let Node::Op {
                    op: inner_op @ (Op::Add | Op::Sub),
                    args: inner_args,
                } = &args[0]
                    && let Some(c1) = args[1].as_const()
                    && let Some(c2) = inner_args[0].as_const()
                {
                    *self = Node::Op {
                        op: *inner_op,
                        args: vec![Node::Const(c2.wrapping_sub(c1)), inner_args[1].clone()],
                    }
                } else if let Node::Op {
                    op: inner_op @ (Op::Add | Op::Sub),
                    args: inner_args,
                } = &args[0]
                    && let Some(c1) = args[1].as_const()
                    && let Some(c2) = inner_args[1].as_const()
                {
                    *self = Node::Op {
                        op: *inner_op,
                        args: vec![
                            inner_args[0].clone(),
                            Node::Const(if *inner_op == Op::Add {
                                c2.wrapping_sub(c1)
                            } else {
                                c2.wrapping_add(c1)
                            }),
                        ],
                    }
                } else if let Node::Op {
                    op: inner_op @ (Op::Add | Op::Sub),
                    args: inner_args,
                } = &args[1]
                    && let Some(c1) = args[0].as_const()
                    && let Some(c2) = inner_args[0].as_const()
                {
                    *self = Node::Op {
                        op: *inner_op,
                        args: vec![Node::Const(c2.wrapping_sub(c1)), inner_args[1].clone()],
                    }
                } else if let Node::Op {
                    op: inner_op @ (Op::Add | Op::Sub),
                    args: inner_args,
                } = &args[1]
                    && let Some(c1) = args[0].as_const()
                    && let Some(c2) = inner_args[1].as_const()
                {
                    *self = Node::Op {
                        op: *inner_op,
                        args: vec![
                            inner_args[0].clone(),
                            Node::Const(if *inner_op == Op::Add {
                                c2.wrapping_sub(c1)
                            } else {
                                c2.wrapping_add(c1)
                            }),
                        ],
                    }
                }
            },
            Op::Mul => {
                if args[0].as_const() == Some(1) {
                    trace!("Eliminating mul with 1 on lhs");
                    *self = args.remove(1);
                } else if args[1].as_const() == Some(1) {
                    trace!("Eliminating mul with 1 on rhs");
                    *self = args.remove(0);
                } else {
                    for n in 0..127 {
                        if args[0].as_const() == Some(1i128 << n) {
                            *self = Node::Op {
                                op: Op::Shl,
                                args: vec![args.remove(1), Node::Const(n)],
                            };
                            break
                        } else if args[1].as_const() == Some(1i128 << n) {
                            *self = Node::Op {
                                op: Op::Shl,
                                args: vec![args.remove(0), Node::Const(n)],
                            };
                            break
                        }
                    }
                }
            },
            Op::UnsignedDiv => {
                if args[1].as_const() == Some(1) {
                    trace!("Eliminating div with 1 on rhs");
                    *self = args.remove(0);
                } else {
                    for n in 0..127 {
                        if args[1].as_const() == Some(1i128 << n) {
                            *self = Node::Op {
                                op: Op::Shr,
                                args: vec![args.remove(0), Node::Const(n)],
                            };
                            break
                        }
                    }
                }
            },
            Op::Div => {
                if args[1].as_const() == Some(1) {
                    trace!("Eliminating div with 1 on rhs");
                    *self = args.remove(0);
                } else if args[0].num_bits() < ALL_BITS {
                    // args[0] *cannot* be negative, because then the rounding works the wrong way..
                    for n in 0..127 {
                        if args[1].as_const() == Some(1i128 << n) {
                            *self = Node::Op {
                                op: Op::Shr,
                                args: vec![args.remove(0), Node::Const(n)],
                            };
                            break
                        }
                    }
                }
            },
            Op::ExtractBits => {
                if let Some(c) = args[1].as_const() {
                    if c == 0 {
                        *self = Node::Const(0);
                    } else {
                        let skip = c.trailing_zeros();
                        let take = (c >> skip).trailing_ones();
                        let mask = bitmask_u128(take) << skip;
                        if c as u128 == mask {
                            *self = Node::Op {
                                op: Op::Select {
                                    num_skip: skip as u8,
                                    num_take: take as u8,
                                },
                                args: vec![args.remove(0)],
                            }
                        }
                    }
                }
            },
            _ => (),
        }
    }

    pub fn propagate_constants(&mut self) {
        if let Node::Op {
            op,
            args,
        } = self
        {
            for arg in args.iter_mut() {
                arg.propagate_constants();
            }

            if args.iter().all(|arg| arg.as_const().is_some()) {
                let mut stack = args.iter().map(|arg| arg.as_const().unwrap()).collect::<ArrayVec<_, 16>>();
                let top_of_stack = stack.pop().unwrap();
                let result = op.eval_from_stack(&|_| unreachable!(), top_of_stack, &mut stack);

                *self = Node::Const(result);
            }
        }
    }

    pub fn create_template(&self, ops: &mut Vec<Op>, arg_interpretation: &mut Vec<Arg>, consts: &mut Vec<i128>) {
        let new_op = match self {
            Node::Arg {
                index,
                num_bits,
                encoding,
            } => {
                let hole = arg_interpretation.len();
                arg_interpretation.push(Arg::Input {
                    index: (*index).try_into().unwrap(),
                    num_bits: (*num_bits).try_into().unwrap(),
                    encoding: *encoding,
                });

                Op::Hole(hole.try_into().unwrap())
            },
            Node::Const(c) => {
                if let Ok(c) = i8::try_from(*c) {
                    Op::Const(c)
                } else {
                    let index = consts.len();
                    consts.push(*c);

                    let hole = arg_interpretation.len();
                    arg_interpretation.push(Arg::Const(index.try_into().unwrap()));

                    Op::Hole(hole.try_into().unwrap())
                }
            },
            Node::Op {
                op,
                args,
            } => {
                for arg in args.iter() {
                    arg.create_template(ops, arg_interpretation, consts);
                }

                *op
            },
        };

        ops.push(new_op);
    }

    fn op(&self) -> Option<Op> {
        match self {
            Node::Op {
                op, ..
            } => Some(*op),
            _ => None,
        }
    }
}

fn mask(num_bits: usize) -> i128 {
    !((-1i128).checked_shl(num_bits as u32).unwrap_or(0))
}

#[derive(Debug)]
pub struct ComputationNormalizer {
    tree: Node,
    original: SynthesizedComputation,
}

impl ComputationNormalizer {
    fn tree_from(ops: &[Op], arg_interpretation: &[Arg], consts: &[i128]) -> Node {
        let mut stack = Vec::new();

        for &op in ops.iter() {
            let args = stack.drain(stack.len() - op.num_args()..).collect();
            stack.push(match op {
                Op::Hole(n) => match arg_interpretation[n as usize] {
                    Arg::Input {
                        index,
                        num_bits,
                        encoding,
                    } => Node::Arg {
                        index: index as usize,
                        num_bits: num_bits as usize,
                        encoding,
                    },
                    Arg::TinyConst(c) => Node::Const(c as i128),
                    Arg::Const(index) => Node::Const(consts[index as usize]),
                },
                Op::Const(c) => Node::Const(c as i128),
                op => Node::Op {
                    op,
                    args,
                },
            });
        }

        stack.pop().unwrap()
    }

    pub fn new(computation: SynthesizedComputation) -> Self {
        Self {
            tree: Self::tree_from(
                computation.expr().ops(),
                computation.arg_interpretation(),
                computation.consts(),
            ),
            original: computation,
        }
    }

    pub fn normalize(&mut self) -> SynthesizedComputation {
        info!("Starting optimization of: {:#?}", self.tree);

        let i = self.original.as_internal();
        self.tree.propagate_constants();

        info!("Constants propagated: {:#?}", self.tree);

        for _ in 0..10 {
            info!("Reducing: {:#?}", self.tree);
            self.tree.reduce(bitmask_u128(i.output_type().num_bits() as u32));
        }

        info!("Reduced: {:#?}", self.tree);

        Self::create_computation(&self.tree, i.output_encoding(), i.output_type())
    }

    fn create_computation(tree: &Node, output_encoding: OutputEncoding, output_type: IoType) -> SynthesizedComputation {
        let mut ops = Vec::new();
        let mut arg_interpretation = Vec::new();
        let mut consts = Vec::new();

        tree.create_template(&mut ops, &mut arg_interpretation, &mut consts);

        let expr = Expression::new(ops);

        SynthesizedComputation::new(
            expr,
            arg_interpretation.into_iter().collect(),
            consts,
            output_encoding,
            output_type,
        )
    }

    pub fn debug_breakage(&mut self, case: &[OwnedValue]) {
        println!("Debugging breakage of: {:#?}", self.tree);

        let i = self.original.as_internal();
        self.tree.propagate_constants();

        for _ in 0..100 {
            println!("Reduction step: {:#?}", self.tree);
            self.tree.reduce(bitmask_u128(i.output_type().num_bits() as u32));

            let current = Self::create_computation(&self.tree, i.output_encoding(), i.output_type());

            println!("Checking {}", current.display(ARG_NAMES));
            if current.evaluate(case) != self.original.evaluate(case) {
                println!("Computation broken");

                // TODO: Try to find the optimization responsible by single-stepping

                return
            } else {
                println!("Computation still OK");
            }
        }

        println!("Done.");
    }
}

#[cfg(test)]
mod tests {
    use liblisa::semantics::default::builder::*;
    use liblisa::semantics::default::computation::{Arg, ArgEncoding, AsComputationRef, OutputEncoding, SynthesizedComputation};
    use liblisa::semantics::default::expr;
    use liblisa::semantics::default::ops::Op;
    use liblisa::semantics::{Computation, IoType, ARG_NAMES};
    use liblisa::value::{OwnedValue, Value};
    use test_log::test;

    use crate::normalizer::ComputationNormalizer;

    /// Little-endian values that aren't a multiple of 8 bits will still fill up a full 8 bits as MSB,
    /// because bytes are rotated. For example:
    ///
    /// 01B3 (9 bits) becomes B301 (16 bits).
    ///
    /// The optimizer needs to account for this in its optimizations
    #[test]
    pub fn bitorder_little_endian() {
        let expr = expr!(select::<8, 8, _, _>(hole::<0>()).sign_extend::<8>()).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 9,
                encoding: ArgEncoding::UnsignedLittleEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Hole(0),
                Op::Select {
                    num_skip: 8,
                    num_take: 8
                },
                Op::SignExtend {
                    num_bits: 8
                },
            ]
        );
    }

    #[test]
    pub fn bitorder_big_endian() {
        let expr = expr!(select::<8, 8, _, _>(hole::<0>()).sign_extend::<8>()).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 9,
                encoding: ArgEncoding::UnsignedBigEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Hole(0),
                Op::Select {
                    num_skip: 8,
                    num_take: 1
                },
            ]
        );
    }

    #[test]
    pub fn constant_propagation() {
        let expr = expr!(or(hole::<0>(), shl(hole::<2>(), hole::<1>().crop::<3>()))).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 16,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::TinyConst(12),
                Arg::TinyConst(5),
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0), Op::Const(80), Op::Or,]);
    }

    #[test]
    pub fn or0_elimination() {
        let expr = expr!(or(hole::<0>(), hole::<1>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 16,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::TinyConst(0),
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0),]);
    }

    #[test]
    pub fn or1_elimination() {
        let expr = expr!(or(hole::<0>(), hole::<1>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 16,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::TinyConst(-1),
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0),]);
        assert_eq!(result.consts(), &[0xffffffff]);
    }

    #[test]
    pub fn and0_elimination() {
        let expr = expr!(and(hole::<0>(), hole::<1>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 16,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::TinyConst(0),
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Const(0),]);
    }

    #[test]
    pub fn and1_elimination() {
        let expr = expr!(and(hole::<0>(), hole::<1>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 16,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::TinyConst(-1),
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0),]);
    }

    #[test]
    pub fn not_and_elimination_lhs() {
        let expr = expr!(not(and(not(hole::<0>()), hole::<1>()))).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 1,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 0,
                    num_bits: 1,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0), Op::Hole(1), Op::Not, Op::Or,]);
    }

    #[test]
    pub fn not_and_elimination_rhs() {
        let expr = expr!(not(and(hole::<0>(), not(hole::<1>())))).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 1,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 0,
                    num_bits: 1,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0), Op::Not, Op::Hole(1), Op::Or,]);
    }

    #[test]
    pub fn not_or_elimination_lhs() {
        let expr = expr!(not(or(not(hole::<0>()), hole::<1>()))).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 1,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 0,
                    num_bits: 1,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0), Op::Hole(1), Op::Not, Op::And,]);
    }

    #[test]
    pub fn not_or_elimination_rhs() {
        let expr = expr!(not(or(hole::<0>(), not(hole::<1>())))).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 1,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 0,
                    num_bits: 1,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0), Op::Not, Op::Hole(1), Op::And,]);
    }

    #[test]
    pub fn and_to_crop_lhs() {
        let expr = expr!(and(hole::<0>(), hole::<1>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Const(0),
                Arg::Input {
                    index: 0,
                    num_bits: 16,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
            ]
            .into_iter()
            .collect(),
            vec![0x3ff],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Hole(0),
                Op::Crop {
                    num_bits: 10
                },
            ]
        );
    }

    #[test]
    pub fn and_to_crop_rhs() {
        let expr = expr!(and(hole::<0>(), hole::<1>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 16,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Const(0),
            ]
            .into_iter()
            .collect(),
            vec![0x3ff],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Hole(0),
                Op::Crop {
                    num_bits: 10
                },
            ]
        );
    }

    #[test]
    pub fn ifzero_elimination_from_condition() {
        let expr = expr!(hole::<0>().if_zero(hole::<1>(), hole::<2>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::TinyConst(0),
                Arg::Input {
                    index: 0,
                    num_bits: 16,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 1,
                    num_bits: 16,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut optimizer = ComputationNormalizer::new(template.clone());
        let result = optimizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0),]);
        assert_eq!(result.arg_interpretation()[0], template.arg_interpretation()[1]);
    }

    #[test]
    pub fn ifzero_elimination_from_result() {
        let expr = expr!(hole::<0>().if_zero(hole::<1>(), hole::<2>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 16,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::TinyConst(1),
                Arg::TinyConst(0),
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0), Op::IsZero,]);
    }

    #[test]
    pub fn ifzero_not_elimination1() {
        let expr = expr!(not(hole::<0>()).crop::<1>().if_zero(hole::<1>(), hole::<2>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 16,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 2,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 1,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Hole(0),
                Op::Crop {
                    num_bits: 1
                },
                Op::Hole(1),
                Op::Hole(2),
                Op::IfZero,
            ]
        );
    }

    #[test]
    pub fn ifzero_not_elimination2() {
        let expr = expr!(select::<13, 1, _, _>(not(hole::<0>())).if_zero(hole::<1>(), hole::<2>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 16,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 2,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 1,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Hole(0),
                Op::Select {
                    num_skip: 13,
                    num_take: 1
                },
                Op::Hole(1),
                Op::Hole(2),
                Op::IfZero,
            ]
        );
    }

    #[test]
    pub fn ifzero_something_else_true_elimination() {
        let expr = expr!(hole::<0>().if_zero(hole::<1>(), c::<1>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 1,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 1,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0), Op::Hole(1), Op::Or,]);
    }

    #[test]
    pub fn ifzero_true_else_something_elimination() {
        let expr = expr!(hole::<0>().if_zero(c::<1>(), hole::<1>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 1,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 1,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0), Op::Not, Op::Hole(1), Op::Or,]);
    }

    #[test]
    pub fn ifzero_true_else_something_elimination_multiple_bits() {
        // IfZero(A, 1, B) & Crop[1](Not(C))
        let expr = expr!(
            and(hole::<0>().if_zero(c::<1>(), hole::<1>()), not(hole::<2>()).crop::<1>()).if_zero(hole::<3>(), hole::<4>())
        )
        .to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 1,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 1,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 2,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 3,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 4,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Hole(0),
                Op::Not,
                Op::Hole(1),
                Op::Or,
                Op::Hole(2),
                Op::Not,
                Op::And,
                Op::Crop {
                    num_bits: 1
                },
                Op::Hole(3),
                Op::Hole(4),
                Op::IfZero,
            ]
        );
    }

    #[test]
    pub fn ifzero_eliminate_chaining_zero_zero() {
        // IfZero(
        //     A,
        //     IfZero(
        //         B,
        //         Y,
        //         X,
        //     ),
        //     Y
        // )
        let expr = expr!(hole::<0>().if_zero(hole::<1>().if_zero(hole::<2>(), hole::<3>(),), hole::<3>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 1,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 1,
                    num_bits: 1,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 2,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 3,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut optimizer = ComputationNormalizer::new(template.clone());
        let result = optimizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        for k in [0, 1] {
            for l in [0, 1] {
                use OwnedValue::Num;
                let inputs = [Num(k), Num(l), Num(0x37), Num(0x55)];
                assert_eq!(template.evaluate(&inputs), result.evaluate(&inputs));
            }
        }

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Hole(0),
                Op::Not,
                Op::Hole(1),
                Op::Not,
                Op::And,
                Op::Crop {
                    num_bits: 1
                },
                Op::Hole(2),
                Op::Hole(3),
                Op::IfZero,
            ]
        );
    }

    #[test]
    pub fn ifzero_eliminate_chaining_zero_nonzero() {
        // IfZero(
        //     A,
        //     IfZero(
        //         B,
        //         X,
        //         Y
        //     ),
        //     Y
        // )
        let expr = expr!(hole::<0>().if_zero(hole::<1>().if_zero(hole::<2>(), hole::<3>(),), hole::<3>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 1,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 1,
                    num_bits: 1,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 2,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 3,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut optimizer = ComputationNormalizer::new(template.clone());
        let result = optimizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        for k in [0, 1] {
            for l in [0, 1] {
                use OwnedValue::Num;
                let inputs = [Num(k), Num(l), Num(0x37), Num(0x55)];
                assert_eq!(template.evaluate(&inputs), result.evaluate(&inputs));
            }
        }

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Hole(0),
                Op::Not,
                Op::Hole(1),
                Op::Not,
                Op::And,
                Op::Crop {
                    num_bits: 1
                },
                Op::Hole(2),
                Op::Hole(3),
                Op::IfZero,
            ]
        );
    }

    #[test]
    pub fn ifzero_eliminate_chaining_nonzero_zero() {
        // IfZero(
        //     A,
        //     Y,
        //     IfZero(
        //         B,
        //         Y,
        //         X
        //     ),
        // )
        let expr = expr!(hole::<0>().if_zero(hole::<3>(), hole::<1>().if_zero(hole::<3>(), hole::<2>(),),)).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 1,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 1,
                    num_bits: 1,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 2,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 3,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut optimizer = ComputationNormalizer::new(template.clone());
        let result = optimizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        for k in [0, 1] {
            for l in [0, 1] {
                use OwnedValue::Num;
                let inputs = [Num(k), Num(l), Num(0x37), Num(0x55)];
                let original_result = template.evaluate(&inputs);
                let optimized_result = result.evaluate(&inputs);
                assert_eq!(original_result, optimized_result);
                println!("{inputs:X?} -> {original_result:?} vs {optimized_result:?}")
            }
        }

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Hole(0),
                Op::Not,
                Op::Crop {
                    num_bits: 1
                },
                Op::Hole(1),
                Op::Not,
                Op::Crop {
                    num_bits: 1
                },
                Op::Or,
                Op::Hole(2),
                Op::Hole(3),
                Op::IfZero,
            ]
        );
    }

    #[test]
    pub fn ifzero_eliminate_chaining_nonzero_nonzero() {
        // IfZero(
        //     A,
        //     Y,
        //     IfZero(
        //         B,
        //         X,
        //         Y
        //     ),
        // )
        let expr = expr!(hole::<0>().if_zero(hole::<3>(), hole::<1>().if_zero(hole::<2>(), hole::<3>(),),)).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 1,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 1,
                    num_bits: 1,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 2,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 3,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut optimizer = ComputationNormalizer::new(template.clone());
        let result = optimizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        for k in [0, 1] {
            for l in [0, 1] {
                use OwnedValue::Num;
                let inputs = [Num(k), Num(l), Num(0x37), Num(0x55)];
                assert_eq!(template.evaluate(&inputs), result.evaluate(&inputs));
            }
        }

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Hole(0),
                Op::Hole(1),
                Op::Not,
                Op::And,
                Op::Hole(2),
                Op::Hole(3),
                Op::IfZero,
            ]
        );
    }

    #[test]
    pub fn ifzero_something_else_false_elimination() {
        let expr = expr!(is_zero(hole::<0>()).if_zero(hole::<1>(), c::<0>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 16,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 1,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[Op::Hole(0), Op::IsZero, Op::Not, Op::Hole(1), Op::And,]
        );
    }

    #[test]
    pub fn ifzero_false_else_something_elimination() {
        let expr = expr!(is_zero(hole::<0>()).if_zero(c::<0>(), hole::<1>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 16,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 1,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0), Op::IsZero, Op::Hole(1), Op::And,]);
    }

    #[test]
    pub fn ifzero_false_else_something_more_than_1_bit_no_elimination() {
        let expr = expr!(is_zero(hole::<0>()).if_zero(c::<0>(), hole::<1>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 16,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 1,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0), Op::Hole(1), Op::Const(0), Op::IfZero,]);
    }

    #[test]
    pub fn ifzero_crop() {
        let expr = expr!(hole::<0>().if_zero(hole::<1>().crop::<32>(), hole::<2>().crop::<32>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 64,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 1,
                    num_bits: 64,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 2,
                    num_bits: 64,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0), Op::Hole(1), Op::Hole(2), Op::IfZero,]);
    }

    #[test]
    pub fn iszero_elimination() {
        let expr = expr!(is_zero(hole::<0>().crop::<1>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 16,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::TinyConst(1),
                Arg::Input {
                    index: 1,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Hole(0),
                Op::Not,
                Op::Crop {
                    num_bits: 1
                },
            ]
        );
    }

    #[test]
    pub fn eliminate_iszero_n_sub_1() {
        let expr = expr!(is_zero(sub(hole::<0>(), c::<1>()))).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 1,
                encoding: ArgEncoding::UnsignedBigEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0),]);
    }

    #[test]
    pub fn transform_sub_to_not() {
        let expr = expr!((sub(hole::<0>(), c::<1>())).crop::<1>()).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 1,
                encoding: ArgEncoding::UnsignedBigEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0), Op::Not,]);
    }

    #[test]
    pub fn transform_add_to_not1() {
        let expr = expr!((add(hole::<0>(), c::<1>())).crop::<1>()).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 1,
                encoding: ArgEncoding::UnsignedBigEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0), Op::Not,]);
    }

    #[test]
    pub fn transform_add_to_not2() {
        let expr = expr!(add(c::<1>(), hole::<0>()).crop::<1>()).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 1,
                encoding: ArgEncoding::UnsignedBigEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0), Op::Not,]);
    }

    #[test]
    pub fn div_to_shr() {
        let expr = expr!(div(hole::<0>(), c::<8>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 16,
                encoding: ArgEncoding::UnsignedLittleEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Hole(0),
                Op::Select {
                    num_skip: 3,
                    num_take: 13
                },
            ]
        );
    }

    #[test]
    pub fn mul_to_shl() {
        let expr = expr!(mul(hole::<0>(), c::<8>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 16,
                encoding: ArgEncoding::SignedLittleEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0), Op::Const(3), Op::Shl,]);
    }

    // TODO: IsZero of single bit
    // TODO: IfZero(Crop[1](), 0, 1) or IfZero(Crop[1](), 1, 0)
    // TODO: XOR with 0
    // TODO: SHL/SHR with 0

    #[test]
    pub fn real_world_1() {
        let expr = expr!((and(
            not(is_zero((shr(mul(hole::<0>(), hole::<1>()), c::<0x3F>())).crop::<64>())),
            not(c::<0>())
        ))
        .crop::<1>()
        .if_zero(c::<0>().crop::<1>(), c::<1>().crop::<1>()))
        .to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 64,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 1,
                    num_bits: 64,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Hole(0),
                Op::Hole(1),
                Op::Mul,
                Op::Select {
                    num_skip: 63,
                    num_take: 64
                },
                Op::IsZero,
                Op::Not,
                Op::Crop {
                    num_bits: 1
                },
            ]
        );
    }

    #[test]
    pub fn retain_crop_for_add_then_select() {
        let expr = expr!(select::<64, 1, _, _>(add(
            hole::<0>().crop::<64>(),
            sub(hole::<1>(), hole::<0>()).crop::<64>()
        )))
        .to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 8,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 1,
                    num_bits: 64,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Hole(0),
                Op::Hole(1),
                Op::Hole(2),
                Op::Sub,
                Op::Crop {
                    num_bits: 64
                },
                Op::Add,
                Op::Select {
                    num_skip: 64,
                    num_take: 1
                },
            ]
        );
    }

    #[test]
    pub fn keep_or_for_div() {
        // Crop { num_bits: 32 }[Div[Or[A, Shl[1, 32]], 2]]
        let expr = expr!(div(or(hole::<0>(), shl(c::<1>(), c::<32>())), c::<2>()).crop::<32>()).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 1,
                    num_bits: 32,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 0,
                    num_bits: 32,
                    encoding: ArgEncoding::SignedLittleEndian,
                },
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Hole(0),
                Op::Hole(1),
                Op::Or,
                Op::Select {
                    num_skip: 1,
                    num_take: 32
                },
            ]
        );
    }

    #[test]
    pub fn keep_crop_after_removing_not_with_multiple_bits() {
        let expr = expr!(((not(hole::<0>().if_zero(c::<1>(), hole::<0>()))).crop::<1>()).if_zero(c::<6>(), c::<7>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 32,
                encoding: ArgEncoding::UnsignedBigEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Hole(0),
                Op::Const(1),
                Op::Hole(1),
                Op::IfZero,
                Op::Crop {
                    num_bits: 1
                },
                Op::Const(7),
                Op::Const(6),
                Op::IfZero,
            ]
        );
    }

    #[test]
    pub fn dont_shift_to_select_if_zext_possible() {
        let expr = expr!(shr(hole::<0>(), c::<32>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 64,
                encoding: ArgEncoding::SignedLittleEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Hole(0),
                Op::Select {
                    num_skip: 32,
                    num_take: 32
                }
            ]
        );

        // =================

        let expr = expr!(is_zero(shr(hole::<0>(), c::<32>()))).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 64,
                encoding: ArgEncoding::SignedLittleEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 32,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0), Op::Const(32), Op::Shr, Op::IsZero,]);
    }

    #[test]
    pub fn resolve_shifts1() {
        // Select[15:+1]((0x1 | (sbe(A) << (1 << 0xC))) >> (0x3 & BitMask(0xC)))
        let expr = expr!(select::<15, 1, _, _>(shr(
            or(c::<0x1>(), shl(hole::<0>(), shl(c::<1>(), c::<0xc>()))),
            and(c::<0x3>(), bit_mask(c::<0xC>()))
        )))
        .to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 128,
                encoding: ArgEncoding::UnsignedBigEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Hole(0),
                Op::Select {
                    num_skip: 18,
                    num_take: 1
                },
            ]
        );
    }

    #[test]
    pub fn resolve_shifts2() {
        // Select[7:+1]((0xD << sbe(A)) >> 0x4)
        let expr = expr!(select::<7, 1, _, _>(shr(shl(c::<0xd>(), hole::<0>()), c::<0x4>()))).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 128,
                encoding: ArgEncoding::UnsignedBigEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Const(0xD),
                Op::Hole(0),
                Op::Shl,
                Op::Select {
                    num_skip: 11,
                    num_take: 1
                },
            ]
        );
    }

    #[test]
    pub fn resolve_shifts3() {
        // Select[15:+1]((0xB << 0x17) >> sbe(A))
        let expr = expr!(select::<15, 1, _, _>(shr(shl(c::<0xb>(), c::<0x17>()), hole::<0>()))).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 128,
                encoding: ArgEncoding::UnsignedBigEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Const(0xD),
                Op::Hole(0),
                Op::Shl,
                Op::Select {
                    num_skip: 11,
                    num_take: 1
                },
            ]
        );

        // Select[7:+1]((0x0 << 0xF) | ((0xB << 0xF) >> sbe(A)))
        let expr = expr!(select::<7, 1, _, _>(shr(shl(c::<0xB>(), c::<0xF>()), hole::<0>()))).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 128,
                encoding: ArgEncoding::UnsignedBigEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Const(0xD),
                Op::Hole(0),
                Op::Shl,
                Op::Select {
                    num_skip: 11,
                    num_take: 1
                },
            ]
        );

        // Select[31:+1]((0x0 << 0x27) | ((0xB << 0x27) >> sbe(A)))
        let expr = expr!(select::<31, 1, _, _>(shr(shl(c::<0xB>(), c::<0x27>()), hole::<0>()))).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 128,
                encoding: ArgEncoding::UnsignedBigEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Const(0xD),
                Op::Hole(0),
                Op::Shl,
                Op::Select {
                    num_skip: 11,
                    num_take: 1
                },
            ]
        );

        // TODO: (0xB >> (0x0 - 0x8)) ^ (0xB >> ((0x0 - 0x8) + sbe(A)))
        // let expr = expr!(
        //     xor(
        //         shr(c::<0xB>(), sub(c::<0>(), c::<8>())),
        //         shr(c::<0xB>(), add(sub(c::<0>(), c::<8>()), hole::<0>()))
        //     )
        // ).to_owned();
        // let template = SynthesizedComputation::new(expr, [
        //     Arg::Input { index: 0, num_bits: 128, encoding: ArgEncoding::UnsignedBigEndian },
        // ].into_iter().collect(), vec![], OutputEncoding::UnsignedLittleEndian, IoType::Integer { num_bits: 1 });

        // println!("{}", template.display(ARG_NAMES));

        // let mut normalizer = ComputationNormalizer::new(template);
        // let result = normalizer.normalize();

        // println!("{}", result.display(ARG_NAMES));

        // assert_eq!(result.expr().ops(), &[
        //     Op::Const(0xD),
        //     Op::Hole(0),
        //     Op::Shl,
        //     Op::Select { num_skip: 11, num_take: 1 },
        // ]);
    }

    #[test]
    pub fn add_sub_chains1() {
        // IsZero((0x7 + (sbe(A) - 0x2F)) - BitMask(0x3))
        let expr = expr!(is_zero(sub(
            add(c::<0x7>(), sub(hole::<0>(), c::<0x2f>())),
            bit_mask(c::<0x3>())
        )))
        .to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 128,
                encoding: ArgEncoding::UnsignedBigEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0), Op::Const(47), Op::Sub, Op::IsZero,]);
    }

    #[test]
    pub fn add_sub_chains2() {
        // IsZero((0x8 + (0x8 + sbe(A))) - BitMask(0x6))
        let expr = expr!(is_zero(sub(
            add(c::<0x8>(), add(c::<0x8>(), hole::<0>())),
            bit_mask(c::<0x6>())
        )))
        .to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 128,
                encoding: ArgEncoding::UnsignedBigEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0), Op::Const(47), Op::Sub, Op::IsZero,]);
    }

    #[test]
    pub fn add_sub_chains3() {
        // IsZero((0x1 - sbe(A)) - 0x28) == IsZero(-0x27 - sbe(A))
        let expr = expr!(is_zero(sub(sub(c::<0x1>(), hole::<0>()), c::<0x28>()))).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 128,
                encoding: ArgEncoding::UnsignedBigEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Const(-0x27), Op::Hole(0), Op::Sub, Op::IsZero,]);
    }

    #[test]
    pub fn merge_or_of_shifts1() {
        // Select[63:+1]((0x5 << sbe(A)) | ((0xE << sbe(A)) >> 0xF))
        let expr = expr!(select::<63, 1, _, _>(or(
            shl(c::<0x5>(), hole::<0>()),
            shr(shl(c::<0xE>(), hole::<0>()), c::<0xF>())
        )))
        .to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 128,
                encoding: ArgEncoding::UnsignedBigEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        const EXPECTED_OUTPUT: &[Op] = &[
            Op::Hole(0),
            Op::Hole(1),
            Op::Shl,
            Op::Select {
                num_skip: 77,
                num_take: 1,
            },
        ];
        const EXPECTED_CONST: i128 = 0x14007;

        assert_eq!(result.expr().ops(), EXPECTED_OUTPUT);
        assert_eq!(result.consts(), &[EXPECTED_CONST,]);

        // Select[63:+1]((0x5 << sbe(A)) | ((0x7 << sbe(A)) >> 0xE))
        let expr = expr!(select::<63, 1, _, _>(or(
            shl(c::<0x5>(), hole::<0>()),
            shr(shl(c::<0x7>(), hole::<0>()), c::<0xE>())
        )))
        .to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 128,
                encoding: ArgEncoding::UnsignedBigEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), EXPECTED_OUTPUT);
        assert_eq!(result.consts(), &[EXPECTED_CONST,]);
    }

    #[test]
    pub fn merge_or_of_shifts2() {
        // Select[7:+1]((0x28 | (0x30 << (1 << 0x5))) >> (sbe(A) & BitMask(0x5)))
        let expr = expr!(select::<7, 1, _, _>(shr(
            or(c::<0x28>(), shl(c::<0x30>(), shl(c::<1>(), c::<0x5>()))),
            and(hole::<0>(), bit_mask(c::<5>()))
        )))
        .to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 128,
                encoding: ArgEncoding::UnsignedBigEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        const EXPECTED_OUTPUT: &[Op] = &[
            Op::Const(3),
            Op::Hole(0),
            Op::Crop {
                num_bits: 5,
            },
            Op::Shl,
            Op::Select {
                num_skip: 30,
                num_take: 1,
            },
        ];

        assert_eq!(result.expr().ops(), EXPECTED_OUTPUT);

        // Select[31:+1](0x0 | (0x6 << Crop[5](sbe(A))))
        let expr = expr!(select::<31, 1, _, _>(or(c::<0>(), shl(c::<0x6>(), hole::<0>().crop::<5>())))).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 128,
                encoding: ArgEncoding::UnsignedBigEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), EXPECTED_OUTPUT);
    }

    #[test]
    pub fn is_zero_double_crop() {
        // IsZero(Crop[32]((sbe(A) >> 0x9) & BitMask(0xA)))
        let expr = expr!(is_zero(
            (and(shr(hole::<0>(), c::<0x9>()), bit_mask(c::<0xA>()))).crop::<32>()
        ))
        .to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 128,
                encoding: ArgEncoding::UnsignedBigEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        const EXPECTED_OUTPUT: &[Op] = &[
            Op::Hole(0),
            Op::Select {
                num_skip: 9,
                num_take: 10,
            },
            Op::IsZero,
        ];

        assert_eq!(result.expr().ops(), EXPECTED_OUTPUT);

        // IsZero(((sbe(A) >> 0x9) & BitMask(0xA)) - (0x0 & BitMask(0xA)))
        let expr = expr!(is_zero(sub(
            and(shr(hole::<0>(), c::<0x9>()), bit_mask(c::<0xA>())),
            and(c::<0>(), bit_mask(c::<0xA>()))
        )))
        .to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 128,
                encoding: ArgEncoding::UnsignedBigEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), EXPECTED_OUTPUT);
    }

    #[test]
    pub fn keep_and_with_const_1() {
        // Select[7:+1]((0x38 | (0x5 << (1 << sbe(A)))) >> (0x1 & BitMask(sbe(A))))
        let expr = expr!(select::<7, 1, _, _>(shr(
            or(c::<0x38>(), shl(c::<0x5>(), shl(c::<1>(), hole::<0>()))),
            and(c::<1>(), bit_mask(hole::<0>()))
        )))
        .to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 128,
                encoding: ArgEncoding::UnsignedBigEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        const EXPECTED_OUTPUT: &[Op] = &[
            Op::Const(5),
            Op::Const(1),
            Op::Hole(0),
            Op::Shl,
            Op::Shl,
            Op::Hole(1),
            Op::BitMask,
            Op::Crop {
                num_bits: 1,
            },
            Op::Shr,
            Op::Select {
                num_skip: 7,
                num_take: 1,
            },
        ];

        assert_eq!(result.expr().ops(), EXPECTED_OUTPUT);
    }

    #[test]
    pub fn keep_xor_term_in_parity() {
        // Parity((0x40 & BitMask(0x7)) ^ (0x2 >> sbe(A)))
        let expr = expr!(parity(xor(
            and(c::<0x40>(), bit_mask(c::<0x7>())),
            shr(c::<0x2>(), hole::<0>()),
        )))
        .to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 128,
                encoding: ArgEncoding::UnsignedBigEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[Op::Const(64), Op::Const(2), Op::Hole(0), Op::Shr, Op::Xor, Op::Parity,]
        );
    }

    #[test]
    pub fn iszero_crop_or_iszero() {
        let expr = expr!(is_zero(
            or(
                is_zero(shr(mul(hole::<0>(), hole::<1>()), hole::<2>())),
                is_zero(not(shr(mul(hole::<0>(), hole::<1>()), hole::<2>())))
            )
            .crop::<64>()
        ))
        .to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 128,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::Input {
                    index: 1,
                    num_bits: 128,
                    encoding: ArgEncoding::UnsignedBigEndian,
                },
                Arg::TinyConst(0x1F),
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Hole(0),
                Op::Hole(1),
                Op::Mul,
                Op::Const(31),
                Op::Shr,
                Op::IsZero,
                Op::Hole(2),
                Op::Hole(3),
                Op::Mul,
                Op::Const(31),
                Op::Shr,
                Op::Not,
                Op::IsZero,
                Op::Or,
                Op::Not,
            ]
        );
    }

    #[test]
    pub fn shift_reduction_with_sle_arg() {
        // IsZero(IsZero(2 & BitMask(1 - Crop[2](sle(F)))))
        // 0 => 0
        // 1 => 0
        // 2 => 1
        // 3 => 1
        let expr = expr!(is_zero(is_zero(and(
            c::<2>(),
            bit_mask(sub(c::<1>(), hole::<0>().crop::<2>()))
        ))))
        .to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 32,
                    encoding: ArgEncoding::SignedLittleEndian,
                },
                Arg::TinyConst(0x1F),
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template);
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Const(3),
                Op::Hole(0),
                Op::Crop {
                    num_bits: 2
                },
                Op::Shl,
                Op::Select {
                    num_skip: 3,
                    num_take: 1
                },
            ]
        );
    }

    #[test]
    pub fn shift_reduction_with_scattered_sle_arg() {
        let expr = expr!(is_zero(sub(
            select::<3, 2, _, _>(hole::<0>()),
            add(select::<8, 1, _, _>(hole::<0>()), select::<18, 1, _, _>(hole::<0>()))
        )))
        .to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [
                Arg::Input {
                    index: 0,
                    num_bits: 32,
                    encoding: ArgEncoding::SignedLittleEndian,
                },
                Arg::TinyConst(0x1F),
            ]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 1,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template.clone());
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[
                Op::Hole(0),
                Op::Hole(1),
                Op::Hole(2),
                Op::ExtractBits,
                Op::Shl,
                Op::Select {
                    num_skip: 123,
                    num_take: 1
                },
            ]
        );

        for x in 0..0xffffff {
            assert_eq!(template.evaluate(&[Value::Num(x)]), result.evaluate(&[Value::Num(x)]));
        }
    }

    #[test]
    pub fn shl_addl_to_or() {
        let expr = expr!(add(c::<1>(), shl(hole::<0>(), c::<1>()))).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 32,
                encoding: ArgEncoding::SignedLittleEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 8,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template.clone());
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[Op::Const(1), Op::Hole(0), Op::Const(1), Op::Shl, Op::Or,]
        );
    }

    #[test]
    pub fn shl_addr_to_or() {
        let expr = expr!(add(shl(hole::<0>(), c::<1>()), c::<1>())).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 32,
                encoding: ArgEncoding::SignedLittleEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 8,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template.clone());
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(
            result.expr().ops(),
            &[Op::Hole(0), Op::Const(1), Op::Shl, Op::Const(1), Op::Or,]
        );
    }

    #[test]
    pub fn eliminate_out_of_range_select_or() {
        let expr = expr!(select::<1, 8, _, _>(or(shl(hole::<0>(), c::<1>()), c::<1>()))).to_owned();
        let template = SynthesizedComputation::new(
            expr,
            [Arg::Input {
                index: 0,
                num_bits: 32,
                encoding: ArgEncoding::SignedLittleEndian,
            }]
            .into_iter()
            .collect(),
            vec![],
            OutputEncoding::UnsignedLittleEndian,
            IoType::Integer {
                num_bits: 8,
            },
        );

        println!("{}", template.display(ARG_NAMES));

        let mut normalizer = ComputationNormalizer::new(template.clone());
        let result = normalizer.normalize();

        println!("{}", result.display(ARG_NAMES));

        assert_eq!(result.expr().ops(), &[Op::Hole(0),]);
    }
}
