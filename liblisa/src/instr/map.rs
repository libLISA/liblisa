use serde::{Deserialize, Serialize};

use super::InstructionFilter;
use crate::instr::Instruction;

#[derive(Clone, Debug)]
struct FilterGroup<T: Clone> {
    filters: [Vec<(InstructionFilter, T)>; 256],
}

impl<T: Clone + Serialize> Serialize for FilterGroup<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.filters.as_slice().serialize(serializer)
    }
}

impl<'de, T: Clone + Deserialize<'de>> Deserialize<'de> for FilterGroup<T> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let v = Vec::<Vec<(InstructionFilter, T)>>::deserialize(deserializer)?;
        Ok(FilterGroup {
            filters: match v.try_into() {
                Ok(arr) => arr,
                Err(_) => panic!("Deserializing a filtergroup with wrong number of entries"),
            },
        })
    }
}

impl<T: Clone + std::fmt::Debug> FilterGroup<T> {
    pub fn new() -> FilterGroup<T> {
        FilterGroup {
            filters: vec![Vec::new(); 256].try_into().unwrap(),
        }
    }
}

/// A map of filters, with faster lookup.
#[derive(Clone, Serialize, Deserialize)]
pub struct FilterMap<T: Clone> {
    filters: [FilterGroup<T>; 16],
}

impl<T: Clone + std::fmt::Debug> FilterMap<T> {
    /// Returns an empty [`FilterMap`].
    pub fn new() -> FilterMap<T> {
        FilterMap {
            filters: vec![FilterGroup::new(); 16].try_into().unwrap(),
        }
    }

    /// Inserts a new entry into the filter map.
    /// Does not overwrite the data of existing filters.
    pub fn add(&mut self, filter: InstructionFilter, data: T) {
        let len = filter.len();
        let b = &filter.data[0];
        if let Some(index) = b.as_value() {
            self.filters[len].filters[index as usize].push((filter, data));
        } else {
            for index in 0..256 {
                if b.matches(index as u8) {
                    self.filters[len].filters[index].push((filter.clone(), data.clone()));
                }
            }
        }
    }

    /// Finds one filter that matches `instruction`, and returns the data associated with this filter.
    pub fn filters(&self, instruction: &Instruction) -> Option<&T> {
        for (filter, data) in self.filters[instruction.byte_len()].filters[instruction.bytes()[0] as usize].iter() {
            if filter.matches(instruction) {
                return Some(data);
            }
        }

        None
    }
}

impl<T: Clone + std::fmt::Debug> Default for FilterMap<T> {
    fn default() -> Self {
        Self::new()
    }
}
