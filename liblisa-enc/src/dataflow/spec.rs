use std::fmt::Debug;
use std::marker::PhantomData;

use itertools::Itertools;
use liblisa::arch::Arch;
use liblisa::state::{StateByte, SystemStateByteView, SystemStateByteViewReg};
use liblisa::utils::bitmap::GrowingBitmap;

use super::IsDataflow;

#[derive(Clone)]
struct Growing2DBitmap {
    data: GrowingBitmap,
}

impl Default for Growing2DBitmap {
    fn default() -> Self {
        Self::new()
    }
}

impl Growing2DBitmap {
    #[inline]
    pub const fn new() -> Self {
        Growing2DBitmap {
            data: GrowingBitmap::new(),
        }
    }

    #[inline]
    fn index(x: usize, y: usize) -> usize {
        let k = x + y;
        (k * (k + 1)) / 2 + x
    }

    #[inline]
    pub fn get(&self, x: usize, y: usize) -> bool {
        self.data.get(Self::index(x, y))
    }

    #[inline]
    pub fn set(&mut self, x: usize, y: usize) {
        let index = Self::index(x, y);
        self.data.set(index);
    }
}

#[derive(Clone)]
pub struct IsDataflowSet {
    sources: Vec<usize>,
    destinations: Vec<usize>,
    data: Vec<IsDataflow>,
    by_source: Vec<Vec<StateByte>>,
    contains: Growing2DBitmap,
}

impl Debug for IsDataflowSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_set().entries(&self.data).finish()
    }
}

impl IsDataflowSet {
    pub const fn new() -> Self {
        IsDataflowSet {
            sources: Vec::new(),
            destinations: Vec::new(),
            data: Vec::new(),
            by_source: Vec::new(),
            contains: Growing2DBitmap::new(),
        }
    }

    pub fn push(&mut self, item: IsDataflow) -> bool {
        if !self.contains.get(item.0.as_usize(), item.1.as_usize()) {
            if self.sources.len() <= item.0.as_usize() {
                self.sources.resize(item.0.as_usize() + 1, 0);
            }

            if self.destinations.len() <= item.1.as_usize() {
                self.destinations.resize(item.1.as_usize() + 1, 0);
            }

            if self.by_source.len() <= item.0.as_usize() {
                self.by_source.resize_with(item.0.as_usize() + 1, Vec::new);
            }

            self.sources[item.0.as_usize()] += 1;
            self.destinations[item.1.as_usize()] += 1;
            self.by_source[item.0.as_usize()].push(item.1);
            self.contains.set(item.0.as_usize(), item.1.as_usize());
            self.data.push(item);

            true
        } else {
            false
        }
    }

    pub fn dests_for_source(&self, source: StateByte) -> impl Iterator<Item = StateByte> + '_ {
        self.by_source
            .get(source.as_usize())
            .map(|dests| dests.iter())
            .into_iter()
            .flatten()
            .copied()
    }

    pub fn iter(&self) -> impl Iterator<Item = &IsDataflow> {
        self.data.iter()
    }
}

pub struct EquivalenceSpecBuilder<A: Arch> {
    data: Vec<Option<Equivalence>>,
    _phantom: PhantomData<A>,
}

impl<A: Arch> EquivalenceSpecBuilder<A> {
    pub fn insert(&mut self, byte: StateByte, value: Equivalence) {
        if byte.as_usize() >= self.data.len() {
            self.data.resize_with(byte.as_usize() + 1, || None);
        }

        self.data[byte.as_usize()] = Some(value);
    }

    pub fn finish(self, view: SystemStateByteView<A>) -> EquivalenceSpec<A> {
        EquivalenceSpec::AllEqBut(AllEqButSpec {
            but: self
                .data
                .into_iter()
                .enumerate()
                .filter(|(_, x)| x.map(|eq| eq != Equivalence::Eq).unwrap_or(false))
                .map(|(index, _)| StateByte::new(index))
                .group_by(|&b| view.as_reg(b).0)
                .into_iter()
                .map(|(reg, items)| {
                    let bytes = items.map(|b| view.as_reg(b).1).collect::<Vec<_>>();
                    let full_mask = bytes
                        .iter()
                        .map(|b| 0xffu64.wrapping_shl(*b as u32 * 8))
                        .fold(0, |a, b| a | b);
                    ButEntry {
                        reg,
                        full_mask,
                        bytes,
                    }
                })
                .collect(),
        })
    }
}

#[derive(Clone)]
pub(crate) struct ButEntry<A: Arch> {
    pub(crate) reg: SystemStateByteViewReg<A::Reg>,
    pub(crate) full_mask: u64,
    pub(crate) bytes: Vec<usize>,
}

#[derive(Clone)]
pub struct AllEqButSpec<A: Arch> {
    but: Vec<ButEntry<A>>,
}

impl<A: Arch> AllEqButSpec<A> {
    pub fn but(&self) -> &[ButEntry<A>] {
        &self.but
    }
}

impl<A: Arch> Debug for AllEqButSpec<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut map = f.debug_struct("AllEqBut");

        for ButEntry {
            reg,
            bytes,
            ..
        } in self.but.iter()
        {
            map.field(&format!("{:?}", (reg, bytes)), &Equivalence::Neq);
        }

        map.finish()
    }
}

#[derive(Clone)]
pub enum EquivalenceSpec<A: Arch> {
    AllEqBut(AllEqButSpec<A>),
}

impl<A: Arch> EquivalenceSpec<A> {
    pub fn build() -> EquivalenceSpecBuilder<A> {
        EquivalenceSpecBuilder {
            data: Vec::new(),
            _phantom: PhantomData,
        }
    }

    pub fn from_neqs(view: SystemStateByteView<A>, neqs: impl Iterator<Item = StateByte>) -> EquivalenceSpec<A> {
        Self::from_reg_pairs(
            neqs.group_by(|&b| view.as_reg(b).0)
                .into_iter()
                .map(|(reg, items)| (reg, items.map(|b| view.as_reg(b).1).collect::<Vec<_>>())),
        )
    }

    pub fn from_reg_pairs(specs: impl Iterator<Item = (SystemStateByteViewReg<A::Reg>, Vec<usize>)>) -> EquivalenceSpec<A> {
        EquivalenceSpec::AllEqBut(AllEqButSpec {
            but: specs
                .map(|(reg, bytes)| ButEntry {
                    reg,
                    full_mask: bytes
                        .iter()
                        .map(|b| 0xffu64.wrapping_shl(*b as u32 * 8))
                        .fold(0, |a, b| a | b),
                    bytes,
                })
                .collect(),
        })
    }

    pub fn bytes<'a>(&'a self, view: &'a SystemStateByteView<'_, A>) -> impl Iterator<Item = StateByte> + 'a {
        match self {
            EquivalenceSpec::AllEqBut(but) => but.but.iter().flat_map(
                |ButEntry {
                     reg,
                     bytes,
                     ..
                 }| bytes.iter().map(|&index| view.reg_to_byte(*reg, index)),
            ),
        }
    }

    #[cfg(debug_assertions)]
    pub fn verify(
        &self, view: SystemStateByteView<A>, base: &liblisa::state::SystemState<A>, modified_in: &liblisa::state::SystemState<A>,
    ) -> bool {
        match self {
            EquivalenceSpec::AllEqBut(but) => {
                for b in (0..view.size()).map(StateByte::new) {
                    let (b_reg, index) = view.as_reg(b);
                    let must_be_equal = but.but.iter().all(
                        |ButEntry {
                             reg,
                             bytes,
                             ..
                         }| reg != &b_reg || !bytes.contains(&index),
                    );
                    if view.get(base, b) == view.get(modified_in, b) {
                        if !must_be_equal {
                            println!("Must be neq: {:?}", view.as_reg(b));
                            return false;
                        }
                    } else if must_be_equal {
                        println!("Must be  eq: {:?}", view.as_reg(b));
                        return false;
                    }
                }

                true
            },
        }
    }
}

impl<A: Arch> Debug for EquivalenceSpec<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EquivalenceSpec::AllEqBut(v) => Debug::fmt(v, f),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Equivalence {
    Eq,
    Neq,
}
