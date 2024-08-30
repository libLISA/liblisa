use std::time::Duration;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use liblisa::encoding::dataflows::AddrTerm;
use rand::{Rng, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

fn is_valid_delta(c: &mut Criterion) {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(0);
    let ts = AddrTerm::all();
    let t = ts[ts.len() - 1];
    c.bench_function("is_valid_delta", |b| {
        b.iter(|| {
            black_box(t.is_valid_delta(rng.gen(), rng.gen(), rng.gen(), rng.gen()));
        })
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default().measurement_time(Duration::from_secs(15));
    targets = is_valid_delta,
}

criterion_main!(benches);
