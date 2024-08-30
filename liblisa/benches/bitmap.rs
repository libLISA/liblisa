use std::time::Duration;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use liblisa::utils::bitmap::GrowingBitmap;

fn bench_get(c: &mut Criterion) {
    let map = GrowingBitmap::new_all_ones(512);
    c.bench_function("GrowingBitmap::get", |b| {
        b.iter(|| {
            black_box(black_box(&map).get(211));
        })
    });
}

fn bench_get_then_reset(c: &mut Criterion) {
    let mut map = GrowingBitmap::new_all_ones(512);
    c.bench_function("GrowingBitmap::get_then_reset", |b| {
        b.iter(|| {
            black_box(black_box(&mut map).get_then_reset(211));
        })
    });
}

fn bench_set(c: &mut Criterion) {
    let mut map = GrowingBitmap::new_all_ones(512);
    c.bench_function("GrowingBitmap::set", |b| {
        b.iter(|| {
            black_box(black_box(&mut map).set(211));
        })
    });
}

fn bench_reset(c: &mut Criterion) {
    let mut map = GrowingBitmap::new_all_ones(512);
    c.bench_function("GrowingBitmap::reset", |b| {
        b.iter(|| {
            black_box(black_box(&mut map).reset(211));
        })
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default().measurement_time(Duration::from_secs(15));
    targets = bench_get, bench_get_then_reset, bench_set, bench_reset
}

criterion_main!(benches);
