use std::collections::{HashMap, HashSet};
use std::fmt::Debug;

use itertools::Itertools;
use liblisa::arch::Arch;
use liblisa::encoding::bitpattern::{FlowValueLocation, PartMapping};
use liblisa::encoding::dataflows::Dest;
use liblisa::encoding::{Encoding, WriteOrdering};
use liblisa::oracle::Oracle;
use liblisa::semantics::Computation;
use liblisa::utils::{bitmask_u64, Symmetric2DMatrix};
use log::{debug, info, trace};
use rand::Rng;

use crate::gen::TestCaseGen;
use crate::output::extract_io;
use crate::SynthesisResult;

#[derive(Debug)]
struct Ordering {
    part_indices: Vec<usize>,
    mappings: HashMap<Vec<Option<u64>>, HashSet<After>>,
    output_indices: Vec<usize>,
}

/// Asserts that `self.0` is written after `self.1`. In other words, `self.0` overwrites (part of) `self.1`.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct After(usize, usize);

impl Debug for After {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{} > #{}", self.0, self.1)
    }
}

/// Determines the [`WriteOrdering`](liblisa::encoding::WriteOrdering)s for an [`Encoding`]'s outputs.
pub fn determine_overlapping_write_order<A: Arch, C: Computation>(
    rng: &mut impl Rng, oracle: &mut impl Oracle<A>, encoding: &Encoding<A, ()>, results: &[SynthesisResult<C>],
) -> Vec<WriteOrdering> {
    let mappable_area = oracle.mappable_area();
    let mut orderings = Vec::new();

    // Determine the cases in which outputs can overlap
    for (_output_index, overlapping) in encoding.overlapping_outputs() {
        info!("Overlapping: {overlapping:?}");
        let parts = encoding
            .parts
            .iter()
            .enumerate()
            .filter(|(_, part)| match &part.mapping {
                PartMapping::Register {
                    locations, ..
                } => overlapping
                    .iter()
                    .any(|&output_index| locations.contains(&FlowValueLocation::Output(output_index))),
                _ => false,
            })
            .collect::<Vec<_>>();

        info!("Parts: {parts:?}");

        let num_bits = parts.iter().map(|&(index, _)| encoding.part_size(index)).sum::<usize>();

        assert!(num_bits <= 24);

        let overlapping_vec = {
            let mut v = overlapping.iter().copied().collect::<Vec<_>>();
            v.sort();
            v
        };

        let mut mappings = HashMap::new();
        for c in 0..1u64 << num_bits {
            let mut val = c;
            let part_values = (0..encoding.parts.len())
                .map(|index| {
                    if let Some((_, part)) = parts.iter().find(|&&(part_index, _)| part_index == index) {
                        let n = val & bitmask_u64(part.size as u32);
                        val >>= part.size;
                        Some(n)
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();

            debug!("c = {c:X?}, part values: {part_values:X?}");

            let invalid = parts.iter().any(|&(part_index, part)| match &part.mapping {
                PartMapping::Register {
                    mapping, ..
                } => part_values[part_index]
                    .map(|value| mapping[value as usize].is_none())
                    .unwrap_or(false),
                _ => unreachable!(),
            });

            if invalid {
                debug!("c = {c:X?} is invalid!");
                continue
            }

            let part_values_ref = &part_values;
            let overlapping = &overlapping;
            let outputs = encoding
                .dataflows
                .outputs
                .iter()
                .enumerate()
                .map(|(output_index, flow)| {
                    if let Some((part_index, mapping)) = encoding
                        .parts
                        .iter()
                        .enumerate()
                        .flat_map(|(index, p)| match &p.mapping {
                            PartMapping::Register {
                                mapping,
                                locations,
                            } if locations.contains(&FlowValueLocation::Output(output_index)) => Some((index, mapping)),
                            _ => None,
                        })
                        .next()
                    {
                        let flow = encoding.dataflows.output_dataflow(output_index);
                        let reg = mapping[part_values_ref[part_index].unwrap() as usize].unwrap();

                        Dest::<A>::Reg(reg, flow.target.size())
                    } else {
                        flow.target
                    }
                })
                .collect::<Vec<_>>();

            let mut is_overlapping = false;
            let mut overlap_matrix = Symmetric2DMatrix::new();
            for (index, output) in outputs.iter().enumerate() {
                for (other_index, other_output) in outputs.iter().enumerate().take(index) {
                    if output.overlaps(other_output) {
                        debug!("{output:?} overlaps {other_output:?}");
                        overlap_matrix.set(index, other_index);
                        is_overlapping = true;
                    }
                }
            }

            if !is_overlapping {
                continue
            }

            let encoding = encoding.instantiate_partially(part_values_ref).unwrap();

            debug!("{c:X} = {encoding}");
            let mut priority = HashSet::new();
            for _ in 0..1000 {
                let gen = TestCaseGen::new_raw(&encoding, &overlapping_vec, rng);
                let gen = gen.as_ref().and_then(|gen| gen.with_mappable_area(&mappable_area, rng));

                if let Some(gen) = gen {
                    for (state_in, state_out) in oracle.batch_observe_iter(gen.iter(rng, 10)) {
                        if let Ok(state_out) = state_out {
                            trace!("{state_in:?} => {state_out:?}");
                            let written = overlapping
                                .iter()
                                .filter(|&&output_index| {
                                    let (inputs, output) = extract_io(
                                        output_index,
                                        gen.instance(),
                                        &state_in.state,
                                        &state_in.part_values,
                                        &state_out,
                                    );
                                    results
                                        .iter()
                                        .find(|result| result.output_index == output_index)
                                        .unwrap()
                                        .computation
                                        .as_ref()
                                        .map(|c| c.compare_eq(&inputs, output))
                                        .unwrap_or(true)
                                })
                                .copied()
                                .collect::<Vec<_>>();
                            let not_written = overlapping
                                .iter()
                                .filter(|output_index| !written.contains(output_index))
                                .copied()
                                .collect::<Vec<_>>();
                            trace!("Written: {written:?}, not written: {not_written:?}");

                            for &written_index in written.iter() {
                                for &not_written_index in not_written.iter() {
                                    if overlap_matrix.get(written_index, not_written_index) {
                                        priority.insert(After(written_index, not_written_index));
                                    }
                                }
                            }
                        }
                    }
                } else {
                    debug!("Failed to create TestCaseGen");
                }
            }

            debug!("Priority = {priority:?}");
            mappings
                .entry(part_values)
                .or_insert(HashSet::new())
                .extend(priority.into_iter());
        }

        orderings.push(Ordering {
            part_indices: parts.iter().map(|&(index, _)| index).collect::<Vec<_>>(),
            output_indices: overlapping_vec,
            mappings,
        });
    }

    // Determine which output takes priority when they overlap
    let mut groups = Vec::new();
    while !orderings.is_empty() {
        let mut group = vec![orderings.pop().unwrap()];

        while let Some(index) = orderings.iter().position(|ordering| {
            ordering
                .output_indices
                .iter()
                .any(|index| group.iter().any(|ordering| ordering.output_indices.contains(index)))
        }) {
            let ordering = orderings.remove(index);
            group.push(ordering);
        }

        groups.push(group);
    }

    let mut combined = Vec::new();
    for group in groups.iter_mut() {
        let part_indices = group[0].part_indices.clone();
        if !group.iter().all(|ordering| ordering.part_indices == part_indices) {
            let _values_by_part = (0..encoding.parts.len())
                .map(|part_index| {
                    group
                        .iter()
                        .flat_map(|ordering| ordering.mappings.keys().map(|key| key[part_index]))
                        .unique()
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            todo!("Handle non-identical part indices")
        }

        let mut combined_ordering = Ordering {
            part_indices,
            mappings: HashMap::new(),
            output_indices: group
                .iter()
                .flat_map(|ordering| ordering.output_indices.iter())
                .copied()
                .unique()
                .collect(),
        };

        for ordering in group.iter() {
            for (k, v) in ordering.mappings.iter() {
                combined_ordering
                    .mappings
                    .entry(k.clone())
                    .or_default()
                    .extend(v.iter().copied())
            }
        }

        combined.push(combined_ordering);
    }

    info!("Determining ordering from: {combined:#?}");

    let mut result = combined
        .iter()
        .flat_map(|ordering| {
            ordering.mappings.iter().map(|(part_values, order)| WriteOrdering {
                part_values: part_values.clone(),
                output_index_order: resolve_order(order).expect("Inconsistent ordering"),
            })
        })
        .collect::<Vec<_>>();

    result.sort_by_key(|o| o.part_values.to_vec());

    info!("Result: {result:#?}");

    result
}

fn resolve_order(order: &HashSet<After>) -> Option<Vec<usize>> {
    let mut order = order.iter().copied().collect::<Vec<_>>();
    let mut output_indices = order.iter().flat_map(|x| [x.0, x.1]).unique().collect::<Vec<_>>();

    let mut result = Vec::new();

    while let Some((next_index, _)) = output_indices
        .iter()
        .enumerate()
        .filter(|(_, &output_index)| !order.iter().any(|v| v.0 == output_index))
        .min_by_key(|&(_, &x)| x)
    {
        let next = output_indices.remove(next_index);
        result.push(next);

        order.retain(|v| v.0 != next && v.1 != next);
    }

    if output_indices.is_empty() {
        Some(result)
    } else {
        None
    }
}
