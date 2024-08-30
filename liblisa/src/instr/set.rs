use log::info;
use serde::{Deserialize, Serialize};

use super::InstructionFilter;
use crate::instr::Instruction;

/// A list of filters.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FilterList {
    filters: Vec<InstructionFilter>,
}

impl FilterList {
    /// Creates an empty list of filters.
    pub fn new() -> Self {
        FilterList {
            filters: Vec::new(),
        }
    }

    /// Returns the number of filters in the list.
    pub fn len(&self) -> usize {
        self.filters.len()
    }

    /// Returns true if the list is empty
    pub fn is_empty(&self) -> bool {
        self.filters.is_empty()
    }

    /// Adds a filter to the list, and attempts to merge this filter with existing filters.
    pub fn add(&mut self, mut filter: InstructionFilter) {
        #[cfg(test)]
        println!("New filter: {filter:?}");
        if let Some(index) = self.filters.iter().position(|f| f.covers(&filter) || f == &filter) {
            // The filter is not necessary, because we already have another filter that filters the same instructions.
            info!(
                "Filter {:?} ignored, because it is redundant with {:?}",
                filter, self.filters[index]
            );
        } else {
            info!("Adding filter: {:?}", filter);
            for f in self.filters.iter_mut() {
                if let Some(new) = f.try_merge(&filter) {
                    if new.covers(f) {
                        *f = new;
                    }
                }
            }

            for f in self.filters.iter() {
                if let Some(new) = filter.try_merge(f) {
                    if new.covers(&filter) {
                        filter = new;
                    }
                }
            }

            self.filters.retain(|f| !filter.covers(f));
            self.filters.push(filter);
        }
    }

    /// Adds a new filter to the list, but does not attempt to merge this filter with existing filters.
    pub fn add_nomerge(&mut self, filter: InstructionFilter) {
        if !self.filters.iter().any(|f| f.covers(&filter)) {
            self.filters.push(filter);
        }
    }

    /// Returns true if there is at least one filter that partially matches `instr`.
    /// This means that all instructions starting with `instr` must have at least one more byte.
    pub fn should_extend(&self, instr: &Instruction) -> bool {
        self.filters
            .iter()
            .any(|f| instr.byte_len() < f.len() && f.matches_smaller_instr_partially(instr))
    }

    /// Returns the filter that matches `instr` if it exists.
    /// Otherwise, returns `None`.
    pub fn matching_filter(&self, instr: &Instruction) -> Option<&InstructionFilter> {
        self.filters
            .iter()
            .rev()
            .find(|filter| filter.matches(instr) && filter.data.iter().skip(instr.byte_len()).all(|bf| bf.mask == 0))
    }

    /// Returns the (lexicographically) next instruction that matches one of the filters in the list.
    pub fn next_matching_instruction(&self, instr: &Instruction) -> Option<Instruction> {
        let mut next = None;
        for filter in self.filters.iter() {
            if let Some(nmi) = filter.next_matching_instruction(instr) {
                if next.map(|next| nmi < next).unwrap_or(true) {
                    next = Some(nmi);
                }
            }
        }

        next
    }
}

impl Default for FilterList {
    fn default() -> Self {
        Self::new()
    }
}
