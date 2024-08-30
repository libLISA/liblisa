use std::cmp::Eq;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

use liblisa::arch::{Arch, Register};
use liblisa::state::{StateByte, SystemStateByteView, SystemStateByteViewReg};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct FlowItem<R> {
    pub reg: SystemStateByteViewReg<R>,
    pub start_byte: usize,
    pub end_byte: usize,
}

impl<R: Debug> Debug for FlowItem<R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}[{}..{}]", self.reg, self.start_byte, self.end_byte)
    }
}

impl<R: Debug + Eq> FlowItem<R> {
    pub fn merge(&mut self, other: &FlowItem<R>) {
        assert_eq!(self.reg, other.reg);
        self.start_byte = self.start_byte.min(other.start_byte);
        self.end_byte = self.end_byte.max(other.end_byte);
    }

    pub fn contains<A: Arch<Reg = R>>(&self, view: SystemStateByteView<A>, b: StateByte) -> bool {
        let (reg, index) = view.as_reg(b);
        reg == self.reg && index >= self.start_byte && index <= self.end_byte
    }
}

#[derive(Clone, PartialEq)]
pub struct Dataflow<R> {
    pub sources: Vec<FlowItem<R>>,
    pub dest: FlowItem<R>,
    pub unobservable_inputs: bool,
}

impl<R: Debug> Debug for Dataflow<R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} => {:?}", self.sources, self.dest)
    }
}

pub fn merge_flowitems<R: Register + Debug + Eq + Hash + Clone>(
    items: impl Iterator<Item = FlowItem<R>>,
) -> impl Iterator<Item = FlowItem<R>> {
    let mut tmp = HashMap::new();
    for item in items {
        tmp.entry((
            item.reg,
            if item.reg.is_flags() {
                (item.start_byte, item.end_byte)
            } else {
                Default::default()
            },
        ))
        .or_insert_with(|| item.clone())
        .merge(&item);
    }

    tmp.into_values()
}

impl<R: Register + Debug + Eq + Hash + Clone> Dataflow<R> {
    pub fn merge(&mut self, other: &Dataflow<R>) {
        self.sources = merge_flowitems(self.sources.iter().cloned().chain(other.sources.iter().cloned())).collect();
        self.dest.merge(&other.dest);
    }
}

impl<R: Register + Eq> Dataflow<R> {
    pub fn sources_equal(&self, other: &Dataflow<R>) -> bool {
        self.sources
            .iter()
            .all(|source| other.sources.iter().any(|other| other == source))
            && other
                .sources
                .iter()
                .all(|source| self.sources.iter().any(|other| other == source))
    }

    pub fn sources_overlap_but_not_equal(&self, other: &Dataflow<R>) -> bool {
        // Check to make sure the sources aren't equal
        if self.sources_equal(other) {
            return false;
        }

        // Check if any sources are overlapping
        for lhs in self.sources.iter() {
            for rhs in other.sources.iter() {
                if lhs.reg == rhs.reg && lhs.start_byte <= rhs.end_byte && rhs.start_byte <= lhs.end_byte
                    // Make sure lhs and rhs are not equal
                    && (lhs.start_byte != rhs.start_byte || lhs.end_byte != rhs.end_byte)
                {
                    return true;
                }
            }
        }

        false
    }

    pub fn num_source_bytes(&self) -> usize {
        self.sources
            .iter()
            .map(|source| source.end_byte - source.start_byte + 1)
            .sum()
    }

    pub fn destinations_overlap(&self, other: &Dataflow<R>) -> bool {
        self.dest.end_byte >= other.dest.start_byte && self.dest.start_byte <= other.dest.end_byte
    }

    pub fn destinations_adjacent(&self, other: &Dataflow<R>) -> bool {
        self.dest.end_byte + 1 == other.dest.start_byte || other.dest.end_byte + 1 == self.dest.start_byte
    }

    pub fn destination_flag_registers_match(&self, other: &Dataflow<R>) -> bool {
        self.dest.reg.is_flags() && self.dest.reg == other.dest.reg
    }
}
