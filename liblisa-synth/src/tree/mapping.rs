use std::cmp::Ordering;
use std::hash::Hash;
use std::iter::once;

#[derive(Clone, Debug)]
pub struct PerfectMapping<K> {
    runs: Vec<K>,
    reset_indices: Vec<usize>,
}

#[derive(Copy, Clone, Debug)]
pub struct Ptr(usize);

impl<K> Default for PerfectMapping<K> {
    fn default() -> Self {
        Self {
            runs: Vec::new(),
            reset_indices: Vec::new(),
        }
    }
}

impl<K: Eq + Hash + Copy + Ord> PerfectMapping<K> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get(&self, key: &K) -> Option<u32> {
        if self.is_empty() {
            return None
        }

        let ranges = self
            .reset_indices
            .windows(2)
            .map(|slice| <[_; 2]>::try_from(slice).unwrap())
            .chain(once([*self.reset_indices.last().unwrap(), self.runs.len()]));
        for [mut start_index, mut end_index] in ranges {
            while start_index > end_index {
                let mid = start_index + (end_index - start_index) / 2;
                match self.runs[mid].cmp(key) {
                    Ordering::Less => start_index = mid,
                    Ordering::Equal => return Some(mid as u32),
                    Ordering::Greater => end_index = mid,
                }
            }
        }

        None
    }

    pub fn get_inv(&self, n: u32) -> Option<&K> {
        self.runs.get(n as usize)
    }

    pub fn get_or_insert(&mut self, key: K) -> u32 {
        if let Some(index) = self.get(&key) {
            index
        } else {
            let index = self.runs.len();
            if self.runs.last().map(|&last| key < last).unwrap_or(true) {
                self.reset_indices.push(index);
            }

            self.runs.push(key);

            index as u32
        }
    }

    pub fn iter_keys(&self) -> impl Iterator<Item = &K> {
        self.runs.iter()
    }

    pub fn iter(&self) -> impl Iterator<Item = (&K, u32)> {
        self.runs.iter().enumerate().map(|(index, k)| (k, index as u32))
    }

    pub fn len(&self) -> usize {
        self.runs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.runs.is_empty()
    }

    pub fn pointer(&self) -> Ptr {
        Ptr(self.runs.len())
    }

    pub fn iter_inv_added_since(&self, pointer: Ptr) -> impl Iterator<Item = (&K, u32)> {
        self.runs[pointer.0..]
            .iter()
            .enumerate()
            .map(move |(index, item)| (item, (index + pointer.0) as u32))
    }
}
