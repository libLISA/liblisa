use liblisa::arch::{Arch, Register};
use liblisa::encoding::bitpattern::{Bit, PartMapping};
use liblisa::encoding::Encoding;
use liblisa::utils::EitherIter;
use log::info;

pub fn remove_useless_bits<A: Arch>(encoding: &mut Encoding<A, ()>) {
    let encoding_ref = &*encoding;
    let bits_to_remove = encoding
        .parts
        .iter()
        .enumerate()
        .flat_map(|(part_index, part)| match &part.mapping {
            PartMapping::Register {
                mapping, ..
            } => Some(EitherIter::Left((0..part.size).flat_map(move |bit_index| {
                let real_bit_index = encoding_ref
                    .bits
                    .iter()
                    .enumerate()
                    .filter(|(_, bit)| bit == &&Bit::Part(part_index))
                    .nth(bit_index)
                    .unwrap()
                    .0;
                let bit_value = encoding_ref.dataflows.instr().nth_bit_from_right(real_bit_index);

                let any_useful = mapping
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| (index >> bit_index) & 1 != bit_value as usize)
                    .any(|(_, reg)| reg.as_ref().map(|reg| !reg.is_zero()).unwrap_or(false));

                if any_useful { None } else { Some(real_bit_index) }
            }))),
            PartMapping::MemoryComputation {
                mapping, ..
            } => Some(EitherIter::Right((0..part.size).flat_map(move |bit_index| {
                let real_bit_index = encoding_ref
                    .bits
                    .iter()
                    .enumerate()
                    .filter(|(_, bit)| bit == &&Bit::Part(part_index))
                    .nth(bit_index)
                    .unwrap()
                    .0;
                let bit_value = encoding_ref.dataflows.instr().nth_bit_from_right(real_bit_index);

                let any_useful = mapping
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| (index >> bit_index) & 1 != bit_value as usize)
                    .any(|(_, computation)| computation.is_some());

                if any_useful { None } else { Some(real_bit_index) }
            }))),
            _ => None,
        })
        .flatten()
        .collect::<Vec<_>>();

    if !bits_to_remove.is_empty() {
        info!(
            "Removing the following bits because they're practically useless: {:?} in {}",
            bits_to_remove, encoding
        );
        for bit_index in bits_to_remove {
            encoding.make_bit_fixed(bit_index).unwrap();
        }

        info!("Result: {}", encoding);
    }
}
