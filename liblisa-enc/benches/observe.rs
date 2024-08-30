use std::iter::repeat;
use std::time::{Duration, Instant};

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use liblisa::arch::x64::X64Arch;
use liblisa::instr::Instruction;
use liblisa::oracle::Oracle;
use liblisa::state::random::random_state;
use liblisa_x64_observer::with_oracle;
use rand::{Rng, SeedableRng};
use rand_xoshiro::Xoshiro256PlusPlus;

fn observe(c: &mut Criterion) {
    with_oracle(|mut o| {
        let instr = Instruction::new(&[0x48, 0x31, 0xD0]);
        let mappable = Oracle::<X64Arch>::mappable_area(&o);

        let mut rng = Xoshiro256PlusPlus::seed_from_u64(rand::thread_rng().gen());
        let page = o.random_mappable_page(&mut rng);
        let pc = page.first_address_after_page() - instr.byte_len() as u64;
        let mut state = random_state::<X64Arch, _, _>(&mut rng, &instr, &mappable, pc.as_u64());
        state.use_trap_flag = false;

        c.bench_function("observe[XOR rax, rdx]", |b| {
            b.iter_custom(|num| {
                let requests = repeat(&state).take(num as usize);
                let start = Instant::now();
                o.batch_observe_iter(requests).for_each(|(_, r)| drop(black_box(r.unwrap())));
                start.elapsed()
            })
        });
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default().measurement_time(Duration::from_secs(15));
    targets = observe
}
criterion_main!(benches);
