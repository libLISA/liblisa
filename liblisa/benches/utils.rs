use std::time::Duration;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use liblisa::utils::{create_from_le_bytes, sign_extend};

fn bench_sign_extend(c: &mut Criterion) {
    c.bench_function("sign_extend", |b| {
        b.iter(|| {
            black_box(sign_extend(black_box(0), black_box(64)));
        })
    });
}

fn bench_u128_from_le_bytes(c: &mut Criterion) {
    for n in 1..=16 {
        let bytes = vec![0x12; n];
        c.bench_function(&format!("u128_from_le_bytes({n} bytes)"), |b| {
            b.iter(|| {
                black_box(create_from_le_bytes(black_box(&bytes), |n| n as i128, |n| n as i128));
            })
        });
    }
}

criterion_group! {
    name = benches;
    config = Criterion::default().measurement_time(Duration::from_secs(15));
    targets = bench_sign_extend, bench_u128_from_le_bytes
}

criterion_main!(benches);
