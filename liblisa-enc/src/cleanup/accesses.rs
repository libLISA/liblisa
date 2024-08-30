use liblisa::arch::Arch;
use liblisa::encoding::bitpattern::{FlowValueLocation, PartMapping};
use liblisa::encoding::dataflows::Dataflows;
use liblisa::encoding::Encoding;
use liblisa::oracle::Oracle;
use log::info;

use crate::cache::EncodingAnalysisCache;
use crate::changes;
use crate::changes::DataflowChange;

pub fn remove_incorrect_memory_computations<A: Arch, O: Oracle<A>>(
    o: &mut O, cache: &impl EncodingAnalysisCache<A>, encoding: &mut Encoding<A, ()>,
) {
    for memory_computation_part_index in 0..encoding.parts.len() {
        let part = &encoding.parts[memory_computation_part_index];
        if let PartMapping::MemoryComputation {
            mapping,
            memory_indexes,
        } = &part.mapping
        {
            let participating_parts = encoding.parts.iter()
                .enumerate()
                .flat_map(|(index, part)| if let PartMapping::Register { locations, mapping } = &part.mapping {
                    if locations.iter().any(|loc| matches!(loc, FlowValueLocation::MemoryAddress { memory_index, .. } if memory_indexes.contains(memory_index))) {
                        Some((index, part, mapping))
                    } else {
                        None
                    }
                } else {
                    None
                })
                .collect::<Vec<_>>();

            info!("Participating parts for {part:?} = {participating_parts:?}");

            let mut invalid_mappings = vec![0; mapping.len()];
            for (reg_part_index, _, part_mapping) in participating_parts.iter() {
                for (computation_val, computation_mapping) in mapping.iter().enumerate() {
                    if computation_mapping.is_some() {
                        for (reg_val, reg_mapping) in part_mapping.iter().enumerate() {
                            if reg_mapping.is_some() {
                                let mut part_values = encoding.extract_parts(encoding.dataflows.instr());
                                part_values[memory_computation_part_index] = computation_val as u64;
                                part_values[*reg_part_index] = reg_val as u64;
                                if let Ok(dataflows) = encoding.instantiate(&part_values) {
                                    info!("Checking {dataflows:?}");
                                    if !check_mapping(cache, o, dataflows, encoding) {
                                        invalid_mappings[computation_val] += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }

            info!("Invalid mapping counts: {invalid_mappings:?}");
            let part = &mut encoding.parts[memory_computation_part_index];
            if let PartMapping::MemoryComputation {
                mapping, ..
            } = &mut part.mapping
            {
                for (invalid, mapping) in invalid_mappings.iter().zip(mapping.iter_mut()) {
                    if *invalid > 0 {
                        *mapping = None;
                    }
                }
            } else {
                unreachable!()
            }
        }
    }

    info!("Remaining encoding: {encoding}");
}

fn check_mapping<A: Arch, O: Oracle<A>>(
    cache: &impl EncodingAnalysisCache<A>, o: &mut O, dataflows: Dataflows<A, ()>, encoding: &Encoding<A, ()>,
) -> bool {
    if let Ok(new_memory_accesses) = cache.infer_accesses(o, dataflows.instr()) {
        info!("New memory accesses: {new_memory_accesses:?}");

        let changes = DataflowChange::compare_memory_accesses(&encoding.dataflows.addresses, &new_memory_accesses);
        let memory_change = DataflowChange::into_change(changes);
        info!("Change after comparing memory accesses: {:?}", memory_change);
        if memory_change.is_invalid_or_error() {
            return false;
        }

        let memory_change = changes::find_memory_access_imm(&encoding.dataflows.addresses, &new_memory_accesses, memory_change);
        if memory_change.is_invalid_or_error() {
            return false;
        }

        info!("Change: {memory_change:?}");
        true
    } else {
        false
    }
}
