#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![feature(const_mut_refs)]
#![feature(generic_arg_infer)]

use std::time::Duration;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use liblisa::semantics::default::builder::*;
use liblisa::semantics::default::computation::{Arg, ArgEncoding, ExprComputation, OutputEncoding};
use liblisa::semantics::default::expr;
use liblisa::semantics::IoType;
use liblisa::value::{AsValue, OwnedValue, Value};
use liblisa_synth::search::InterpretedArgs;
use rand::seq::SliceRandom;
use rand::{Rng, RngCore, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

fn interpret_inputs(c: &mut Criterion) {
    let arg = Arg::Input {
        index: 0,
        num_bits: 64,
        encoding: ArgEncoding::SignedBigEndian,
    };
    let inputs = &[OwnedValue::Num(0x1234321), OwnedValue::Num(0x1234321)];
    c.bench_function("Arg::interpret_inputs(sbe_64b_int)", |b| {
        b.iter(|| black_box(arg.interpret_inputs(inputs, &[])))
    });

    let arg = Arg::Input {
        index: 0,
        num_bits: 64,
        encoding: ArgEncoding::SignedLittleEndian,
    };
    let inputs = &[OwnedValue::Num(0x1234321), OwnedValue::Num(0x1234321)];
    c.bench_function("Arg::interpret_inputs(sle_64b_int)", |b| {
        b.iter(|| black_box(arg.interpret_inputs(inputs, &[])))
    });

    let arg = Arg::Input {
        index: 0,
        num_bits: 64,
        encoding: ArgEncoding::UnsignedBigEndian,
    };
    let inputs = &[OwnedValue::Num(0x1234321), OwnedValue::Num(0x1234321)];
    c.bench_function("Arg::interpret_inputs(ube_64b_int)", |b| {
        b.iter(|| black_box(arg.interpret_inputs(inputs, &[])))
    });

    let arg = Arg::Input {
        index: 0,
        num_bits: 64,
        encoding: ArgEncoding::SignedLittleEndian,
    };
    let inputs = &[OwnedValue::Num(0x1234321), OwnedValue::Num(0x1234321)];
    c.bench_function("Arg::interpret_inputs(ule_64b_int)", |b| {
        b.iter(|| black_box(arg.interpret_inputs(inputs, &[])))
    });

    let arg = Arg::Input {
        index: 0,
        num_bits: 64,
        encoding: ArgEncoding::SignedBigEndian,
    };
    let inputs = &[
        OwnedValue::Bytes(vec![0xf3, 0x20, 0xc7, 0x33, 0x00, 0x01, 0x9a, 0xdb]),
        OwnedValue::Bytes(vec![0xf3, 0x20, 0xc7, 0x33, 0x00, 0x01, 0x9a, 0xdb]),
    ];
    c.bench_function("Arg::interpret_inputs(sbe_64b_bytes)", |b| {
        b.iter(|| black_box(arg.interpret_inputs(inputs, &[])))
    });

    let arg = Arg::Input {
        index: 0,
        num_bits: 64,
        encoding: ArgEncoding::SignedLittleEndian,
    };
    let inputs = &[
        OwnedValue::Bytes(vec![0xf3, 0x20, 0xc7, 0x33, 0x00, 0x01, 0x9a, 0xdb]),
        OwnedValue::Bytes(vec![0xf3, 0x20, 0xc7, 0x33, 0x00, 0x01, 0x9a, 0xdb]),
    ];
    c.bench_function("Arg::interpret_inputs(sle_64b_bytes)", |b| {
        b.iter(|| black_box(arg.interpret_inputs(inputs, &[])))
    });

    let arg = Arg::Input {
        index: 0,
        num_bits: 64,
        encoding: ArgEncoding::UnsignedBigEndian,
    };
    let inputs = &[
        OwnedValue::Bytes(vec![0xf3, 0x20, 0xc7, 0x33, 0x00, 0x01, 0x9a, 0xdb]),
        OwnedValue::Bytes(vec![0xf3, 0x20, 0xc7, 0x33, 0x00, 0x01, 0x9a, 0xdb]),
    ];
    c.bench_function("Arg::interpret_inputs(ube_64b_bytes)", |b| {
        b.iter(|| black_box(arg.interpret_inputs(inputs, &[])))
    });

    let arg = Arg::Input {
        index: 0,
        num_bits: 64,
        encoding: ArgEncoding::SignedLittleEndian,
    };
    let inputs = &[
        OwnedValue::Bytes(vec![0xf3, 0x20, 0xc7, 0x33, 0x00, 0x01, 0x9a, 0xdb]),
        OwnedValue::Bytes(vec![0xf3, 0x20, 0xc7, 0x33, 0x00, 0x01, 0x9a, 0xdb]),
    ];
    c.bench_function("Arg::interpret_inputs(ule_64b_bytes)", |b| {
        b.iter(|| black_box(arg.interpret_inputs(inputs, &[])))
    });

    let arg = Arg::TinyConst(0);
    c.bench_function("Arg::interpret_inputs(const)", |b| {
        b.iter(|| black_box(arg.interpret_inputs(inputs, &[])))
    });
}

fn evaluate(crit: &mut Criterion) {
    let inputs = &[OwnedValue::Num(0x1234321), OwnedValue::Num(0x1234321), OwnedValue::Num(5)];
    let args = vec![
        Arg::Input {
            index: 0,
            num_bits: 64,
            encoding: ArgEncoding::SignedBigEndian,
        },
        Arg::Input {
            index: 1,
            num_bits: 64,
            encoding: ArgEncoding::SignedBigEndian,
        },
        Arg::Input {
            index: 2,
            num_bits: 64,
            encoding: ArgEncoding::SignedBigEndian,
        },
    ];
    let interpreted_args = InterpretedArgs::from_arg_list(&args, inputs);

    let template = expr!(not(is_zero(xor(
        (mul(hole::<0>(), hole::<1>())).sign_extend::<64>(),
        mul(hole::<0>(), hole::<1>())
    ))));
    let template = ExprComputation::new(
        template.without_fast_eval(),
        OutputEncoding::UnsignedBigEndian,
        IoType::Integer {
            num_bits: 1,
        },
    );
    let arg_indices = black_box(vec![0u16, 1]);
    crit.bench_function("evaluate::mul_cf", |b| {
        b.iter(|| black_box(template.evaluate_with_args_indirect(interpreted_args.as_slice(), &arg_indices)))
    });

    let template = expr!(hole::<1>().crop::<6>().if_zero(
        hole::<2>(),
        xor(
            select::<63, 1, _, _>(hole::<0>().rol::<64, _, _>(sub(c::<64>(), hole::<1>().crop::<6>()))),
            select::<62, 1, _, _>(hole::<0>().rol::<64, _, _>(sub(c::<64>(), hole::<1>().crop::<6>())))
        )
    ));
    let template = ExprComputation::new(
        template.without_fast_eval(),
        OutputEncoding::UnsignedBigEndian,
        IoType::Integer {
            num_bits: 1,
        },
    );
    let arg_indices = black_box(vec![0u16, 1, 2]);
    crit.bench_function("evaluate::complex_bool", |b| {
        b.iter(|| black_box(template.evaluate_with_args_indirect(interpreted_args.as_slice(), &arg_indices)))
    });

    let template = expr!(xor(
        select::<32, 1, _, _>(add(
            hole::<0>().crop::<32>(),
            sub(c::<0>(), add(hole::<1>(), hole::<2>())).crop::<32>()
        )),
        select::<31, 1, _, _>(add(
            hole::<0>().crop::<31>(),
            sub(zero(), add(hole::<1>(), hole::<2>())).crop::<31>()
        ))
    ));
    let template = ExprComputation::new(
        template.without_fast_eval(),
        OutputEncoding::UnsignedBigEndian,
        IoType::Integer {
            num_bits: 1,
        },
    );
    let arg_indices = black_box(vec![0u16, 1, 2]);
    crit.bench_function("evaluate::sbb_ov", |b| {
        b.iter(|| black_box(template.evaluate_with_args_indirect(interpreted_args.as_slice(), &arg_indices)))
    });
}

fn evaluate_fast(crit: &mut Criterion) {
    let inputs = &[OwnedValue::Num(0x1234321), OwnedValue::Num(0x1234321), OwnedValue::Num(5)];
    let args = vec![
        Arg::Input {
            index: 0,
            num_bits: 64,
            encoding: ArgEncoding::SignedBigEndian,
        },
        Arg::Input {
            index: 1,
            num_bits: 64,
            encoding: ArgEncoding::SignedBigEndian,
        },
        Arg::Input {
            index: 2,
            num_bits: 64,
            encoding: ArgEncoding::SignedBigEndian,
        },
    ];
    let interpreted_args = InterpretedArgs::from_arg_list(&args, inputs);

    let expr = expr!(not(is_zero(xor(
        (mul(hole::<0>(), hole::<1>())).sign_extend::<64>(),
        mul(hole::<0>(), hole::<1>())
    ))));
    let template = ExprComputation::new(
        expr,
        OutputEncoding::UnsignedBigEndian,
        IoType::Integer {
            num_bits: 1,
        },
    );
    let arg_indices = black_box(vec![0u16, 1]);
    crit.bench_function("evaluate_fast::mul_cf", |b| {
        b.iter(|| black_box(template.evaluate_with_args_indirect(interpreted_args.as_slice(), &arg_indices)))
    });

    let expr = expr!(hole::<1>().crop::<6>().if_zero(
        hole::<2>(),
        xor(
            select::<63, 1, _, _>(hole::<0>().rol::<64, _, _>(sub(c::<64>(), hole::<1>().crop::<6>()))),
            select::<62, 1, _, _>(hole::<0>().rol::<64, _, _>(sub(c::<64>(), hole::<1>().crop::<6>())))
        )
    ));
    let template = ExprComputation::new(
        expr,
        OutputEncoding::UnsignedBigEndian,
        IoType::Integer {
            num_bits: 1,
        },
    );
    let arg_indices = black_box(vec![0u16, 1, 2]);
    crit.bench_function("evaluate_fast::complex_bool", |b| {
        b.iter(|| black_box(template.evaluate_with_args_indirect(interpreted_args.as_slice(), &arg_indices)))
    });

    let expr = expr!(xor(
        select::<32, 1, _, _>(add(
            hole::<0>().crop::<32>(),
            sub(c::<0>(), add(hole::<1>(), hole::<2>())).crop::<32>()
        )),
        select::<31, 1, _, _>(add(
            hole::<0>().crop::<31>(),
            sub(zero(), add(hole::<1>(), hole::<2>())).crop::<31>()
        ))
    ));
    let template = ExprComputation::new(
        expr,
        OutputEncoding::UnsignedBigEndian,
        IoType::Integer {
            num_bits: 1,
        },
    );
    let arg_indices = black_box(vec![0u16, 1, 2]);
    crit.bench_function("evaluate_fast::sbb_ov", |b| {
        b.iter(|| black_box(template.evaluate_with_args_indirect(interpreted_args.as_slice(), &arg_indices)))
    });
}

fn evaluate_compare_eq(crit: &mut Criterion) {
    let inputs = &[OwnedValue::Num(0x1234321), OwnedValue::Num(0x1234321), OwnedValue::Num(5)];
    let args = vec![
        Arg::Input {
            index: 0,
            num_bits: 64,
            encoding: ArgEncoding::SignedBigEndian,
        },
        Arg::Input {
            index: 1,
            num_bits: 64,
            encoding: ArgEncoding::SignedBigEndian,
        },
        Arg::Input {
            index: 2,
            num_bits: 64,
            encoding: ArgEncoding::SignedBigEndian,
        },
    ];
    let interpreted_args = InterpretedArgs::from_arg_list(&args, inputs);

    let expr = expr!(not(is_zero(xor(
        (mul(hole::<0>(), hole::<1>())).sign_extend::<64>(),
        mul(hole::<0>(), hole::<1>())
    ))));
    let template = ExprComputation::new(
        expr,
        OutputEncoding::UnsignedBigEndian,
        IoType::Integer {
            num_bits: 64,
        },
    );
    let arg_indices = black_box(vec![0u16, 1]);
    crit.bench_function("evaluate_fast_compare_eq_num::mul_cf", |b| {
        b.iter(|| {
            black_box(template.compare_eq_with_args_indirect(
                interpreted_args.as_slice(),
                &arg_indices,
                black_box(Value::Num(0x123)),
            ))
        })
    });

    let expr = expr!(hole::<1>().crop::<6>().if_zero(
        hole::<2>(),
        xor(
            select::<63, 1, _, _>(hole::<0>().rol::<64, _, _>(sub(c::<64>(), hole::<1>().crop::<6>()))),
            select::<62, 1, _, _>(hole::<0>().rol::<64, _, _>(sub(c::<64>(), hole::<1>().crop::<6>())))
        )
    ));
    let template = ExprComputation::new(
        expr,
        OutputEncoding::UnsignedBigEndian,
        IoType::Integer {
            num_bits: 64,
        },
    );
    let arg_indices = black_box(vec![0u16, 1, 2]);
    crit.bench_function("evaluate_fast_compare_eq_num::complex_bool", |b| {
        b.iter(|| {
            black_box(template.compare_eq_with_args_indirect(
                interpreted_args.as_slice(),
                &arg_indices,
                black_box(Value::Num(0x123)),
            ))
        })
    });

    let expr = expr!(xor(
        select::<32, 1, _, _>(add(
            hole::<0>().crop::<32>(),
            sub(c::<0>(), add(hole::<1>(), hole::<2>())).crop::<32>()
        )),
        select::<31, 1, _, _>(add(
            hole::<0>().crop::<31>(),
            sub(zero(), add(hole::<1>(), hole::<2>())).crop::<31>()
        ))
    ));
    let template = ExprComputation::new(
        expr,
        OutputEncoding::UnsignedBigEndian,
        IoType::Integer {
            num_bits: 64,
        },
    );
    let arg_indices = black_box(vec![0u16, 1, 2]);
    crit.bench_function("evaluate_fast_compare_eq_num::sbb_ov", |b| {
        b.iter(|| {
            black_box(template.compare_eq_with_args_indirect(
                interpreted_args.as_slice(),
                &arg_indices,
                black_box(Value::Num(0x123)),
            ))
        })
    });

    let mut rng = Xoshiro256PlusPlus::seed_from_u64(rand::thread_rng().gen());
    let inputs = &[OwnedValue::Num(0x1234321), OwnedValue::Num(0x1234321), OwnedValue::Num(5)];
    let args = vec![
        Arg::Input {
            index: 0,
            num_bits: 64,
            encoding: ArgEncoding::SignedBigEndian,
        },
        Arg::Input {
            index: 1,
            num_bits: 64,
            encoding: ArgEncoding::SignedBigEndian,
        },
        Arg::Input {
            index: 2,
            num_bits: 64,
            encoding: ArgEncoding::SignedBigEndian,
        },
    ];
    let interpreted_args = InterpretedArgs::from_arg_list(&args, inputs);

    let expected = black_box(
        (0..1000)
            .map(|_| {
                let mut bytes = [0u8; 8];
                rng.fill_bytes(&mut bytes);
                OwnedValue::Bytes(bytes.to_vec())
            })
            .collect::<Vec<_>>(),
    );

    let expr = expr!(not(is_zero(xor(
        (mul(hole::<0>(), hole::<1>())).sign_extend::<64>(),
        mul(hole::<0>(), hole::<1>())
    ))));
    let template = black_box(ExprComputation::new(
        expr,
        OutputEncoding::UnsignedBigEndian,
        IoType::Bytes {
            num_bytes: 8,
        },
    ));
    let arg_indices = black_box(vec![0u16, 1]);
    crit.bench_function("evaluate_fast_compare_eq_bytes::mul_cf", |b| {
        b.iter(|| {
            black_box(template.compare_eq_with_args_indirect(
                black_box(interpreted_args.as_slice()),
                black_box(&arg_indices),
                expected.choose(&mut rng).unwrap().as_value(),
            ))
        })
    });

    let expr = expr!(hole::<1>().crop::<6>().if_zero(
        hole::<2>(),
        xor(
            select::<63, 1, _, _>(hole::<0>().rol::<64, _, _>(sub(c::<64>(), hole::<1>().crop::<6>()))),
            select::<62, 1, _, _>(hole::<0>().rol::<64, _, _>(sub(c::<64>(), hole::<1>().crop::<6>())))
        )
    ));
    let template = black_box(ExprComputation::new(
        expr,
        OutputEncoding::UnsignedBigEndian,
        IoType::Bytes {
            num_bytes: 8,
        },
    ));
    let arg_indices = black_box(vec![0u16, 1, 2]);
    crit.bench_function("evaluate_fast_compare_eq_bytes::complex_bool", |b| {
        b.iter(|| {
            black_box(template.compare_eq_with_args_indirect(
                black_box(interpreted_args.as_slice()),
                black_box(&arg_indices),
                expected.choose(&mut rng).unwrap().as_value(),
            ))
        })
    });

    let expr = expr!(xor(
        select::<32, 1, _, _>(add(
            hole::<0>().crop::<32>(),
            sub(c::<0>(), add(hole::<1>(), hole::<2>())).crop::<32>()
        )),
        select::<31, 1, _, _>(add(
            hole::<0>().crop::<31>(),
            sub(zero(), add(hole::<1>(), hole::<2>())).crop::<31>()
        ))
    ));
    let template = black_box(ExprComputation::new(
        expr,
        OutputEncoding::UnsignedBigEndian,
        IoType::Bytes {
            num_bytes: 8,
        },
    ));
    let arg_indices = black_box(vec![0u16, 1, 2]);
    crit.bench_function("evaluate_fast_compare_eq_bytes::sbb_ov", |b| {
        b.iter(|| {
            black_box(template.compare_eq_with_args_indirect(
                black_box(interpreted_args.as_slice()),
                black_box(&arg_indices),
                expected.choose(&mut rng).unwrap().as_value(),
            ))
        })
    });
}

criterion_group!(
    name = benches;
    config = Criterion::default().measurement_time(Duration::from_secs(30)).sample_size(1000);
    targets = evaluate, evaluate_fast, interpret_inputs, evaluate_compare_eq
);
criterion_main!(benches);
