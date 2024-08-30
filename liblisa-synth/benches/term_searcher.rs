use std::time::Duration;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use liblisa::semantics::IoType;
use liblisa::value::OwnedValue;
use liblisa_synth::search::termsearcher::BoolTermSearcher;
use liblisa_synth::{Synthesizer, SynthesizerBase};

fn single_template_search(c: &mut Criterion) {
    c.bench_function("TermSearcher", |b| {
        b.iter(|| {
            let mut t = BoolTermSearcher::new(
                &[
                    IoType::Integer {
                        num_bits: 64,
                    },
                    IoType::Integer {
                        num_bits: 64,
                    },
                ],
                IoType::Integer {
                    num_bits: 1,
                },
            );

            use OwnedValue::*;

            let match_true = [
                [Num(0x0), Num(0xD48765C89B2)],
                [Num(0x4000000000000000), Num(0xD48765C89B2)],
                [Num(0x4000000000000000), Num(0xD48765C89B2)],
                [Num(0x0), Num(0x69818482BFF60BA0)],
                [Num(0x0), Num(0x69818482BFF60BA0)],
                [Num(0xFFFFFFFFFFFF860B), Num(0xD48765C89B2)],
                [Num(0xFFFFFFFFFFFF860B), Num(0xD48765C89B2)],
                [Num(0xFFFFFFFFFFFF860B), Num(0xD48765C89B2)],
                [Num(0x0), Num(0x8000000000000000)],
                [Num(0x0), Num(0x8000000000000000)],
                [Num(0x0), Num(0x8000000000000000)],
                [Num(0xFFFFFFFFFFFF860B), Num(0x69818482BFF60BA0)],
                [Num(0xFFFFFFFFFFFF860B), Num(0x69818482BFF60BA0)],
                [Num(0xFFFFFFFFFFFF860B), Num(0x69818482BFF60BA0)],
                [Num(0x4000000000000000), Num(0x8000000000000000)],
                [Num(0x4000000000000000), Num(0x8000000000000000)],
                [Num(0x4000000000000000), Num(0x8000000000000000)],
                [Num(0xA525C00000000000), Num(0xD48765C89B2)],
                [Num(0xA525C00000000000), Num(0xD48765C89B2)],
                [Num(0xA525C00000000000), Num(0xD48765C89B2)],
                [Num(0xA525C00000000000), Num(0xD48765C89B2)],
                [Num(0x0), Num(0xBDFFFFFFFFFFFFFF)],
                [Num(0x0), Num(0xBDFFFFFFFFFFFFFF)],
                [Num(0x0), Num(0xBDFFFFFFFFFFFFFF)],
                [Num(0x0), Num(0xBDFFFFFFFFFFFFFF)],
                [Num(0xA525C00000000000), Num(0x69818482BFF60BA0)],
                [Num(0xA525C00000000000), Num(0x69818482BFF60BA0)],
                [Num(0xA525C00000000000), Num(0x69818482BFF60BA0)],
                [Num(0xA525C00000000000), Num(0x69818482BFF60BA0)],
                [Num(0x4000000000000000), Num(0xBDFFFFFFFFFFFFFF)],
                [Num(0x4000000000000000), Num(0xBDFFFFFFFFFFFFFF)],
                [Num(0x4000000000000000), Num(0xBDFFFFFFFFFFFFFF)],
                [Num(0x4000000000000000), Num(0xBDFFFFFFFFFFFFFF)],
                [Num(0xFFFFFFFFFFFF860B), Num(0xBDFFFFFFFFFFFFFF)],
                [Num(0xFFFFFFFFFFFF860B), Num(0xBDFFFFFFFFFFFFFF)],
                [Num(0xFFFFFFFFFFFF860B), Num(0xBDFFFFFFFFFFFFFF)],
                [Num(0xFFFFFFFFFFFF860B), Num(0xBDFFFFFFFFFFFFFF)],
                [Num(0x80BB83F8DD4EDFFF), Num(0xFFFFFFFFB9A08B02)],
            ];
            let match_false = [
                [Num(0x4000000000000000), Num(0x69818482BFF60BA0)],
                [Num(0x7E35000000000000), Num(0x7FFFFFFFFFFFFFFF)],
                [Num(0xA525C00000000000), Num(0x8000000000000000)],
                [Num(0xA525C00000000000), Num(0xBDFFFFFFFFFFFFFF)],
                [Num(0xFFFFFFFFFFFF860B), Num(0x8000000000000000)],
            ];

            for case in match_true.into_iter() {
                t.add_case(&case, true);
            }

            for case in match_false.into_iter() {
                t.add_case(&case, false);
            }

            black_box(t)
        })
    });
}

criterion_group!(
    name = benches;
    config = Criterion::default().measurement_time(Duration::from_secs(30)).sample_size(10);
    targets = single_template_search
);
criterion_main!(benches);
