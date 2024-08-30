use std::str::FromStr;
use std::time::Duration;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use liblisa::instr::Instruction;
use liblisa_enc::random_instr_bytes;
use rand::{Rng, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

fn randomize_bytes(c: &mut Criterion) {
    let mut rng = Xoshiro256PlusPlus::seed_from_u64(rand::thread_rng().gen());
    let start = Instruction::from_str("420F00B000000000").unwrap();

    c.bench_function("randomize_bytes", |b| {
        b.iter(|| black_box(random_instr_bytes(&mut rng, start, None)))
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default().measurement_time(Duration::from_secs(15));
    targets = randomize_bytes
}
criterion_main!(benches);
