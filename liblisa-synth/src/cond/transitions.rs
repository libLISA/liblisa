use std::fmt;
use std::num::NonZeroU8;

use arrayvec::ArrayVec;
use liblisa::utils::bitmap::GrowingBitmap;
use liblisa::utils::EitherIter;
use liblisa::value::{AsValue, OwnedValue};
use log::debug;

use super::casemap::CaseMap;
use super::MAX_INPUTS;
use crate::Requester;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TransitionMap {
    Tiny(Vec<Option<NonZeroU8>>),
    Full(Vec<Option<CaseMap>>),
}

impl TransitionMap {
    #[must_use]
    pub fn len(&self) -> usize {
        match self {
            TransitionMap::Tiny(v) => v.len(),
            TransitionMap::Full(v) => v.len(),
        }
    }

    #[must_use]
    pub fn overlaps(&self, transition_map: &TransitionMap) -> bool {
        transition_map.iter().zip(self.iter()).all(|(a, b)| match (a, b) {
            (Some(a), Some(b)) => a.overlaps(b),
            (None, None) => true,
            _ => false,
        })
    }

    #[must_use]
    pub fn get(&self, index: usize) -> Option<CaseMap> {
        match self {
            TransitionMap::Tiny(v) => v[index].map(|m| CaseMap::new_from_u64(m.get() as u64)),
            TransitionMap::Full(v) => v[index],
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = Option<CaseMap>> + '_ {
        match self {
            TransitionMap::Tiny(v) => {
                EitherIter::Left(v.iter().copied().map(|m| m.map(|m| CaseMap::new_from_u64(m.get() as u64))))
            },
            TransitionMap::Full(v) => EitherIter::Right(v.iter().copied()),
        }
    }

    fn create_tiny(item: Option<CaseMap>) -> Option<Option<NonZeroU8>> {
        if item.map(|m| m.as_u64() != 0 && m.as_u64() <= u8::MAX as u64).unwrap_or(true) {
            Some(item.map(|m| NonZeroU8::new(m.as_u64() as u8).unwrap()))
        } else {
            None
        }
    }

    fn push(&mut self, item: Option<CaseMap>) {
        match (item, &mut *self) {
            (m, TransitionMap::Tiny(v)) => {
                if let Some(m) = Self::create_tiny(m) {
                    v.push(m)
                } else {
                    self.as_full().push(m);
                }
            },
            (m, TransitionMap::Full(v)) => v.push(m),
        }
    }

    fn as_full(&mut self) -> &mut Vec<Option<CaseMap>> {
        if let TransitionMap::Full(v) = self {
            v
        } else {
            *self = TransitionMap::Full(self.iter().collect());

            match self {
                TransitionMap::Full(v) => v,
                _ => unreachable!(),
            }
        }
    }

    pub fn restrict_to(&mut self, other: &TransitionMap) {
        match self {
            TransitionMap::Tiny(v) => {
                for (item, restrict) in v.iter_mut().zip(other.iter()) {
                    let mut unpacked_item = item.map(|m| CaseMap::new_from_u64(m.get() as u64));
                    if let (Some(item), Some(restrict)) = (unpacked_item.as_mut(), restrict) {
                        item.restrict_to(restrict)
                    }

                    *item = Self::create_tiny(unpacked_item).unwrap();
                }
            },
            TransitionMap::Full(v) => {
                for (item, restrict) in v.iter_mut().zip(other.iter()) {
                    if let (Some(item), Some(restrict)) = (item.as_mut(), restrict) {
                        item.restrict_to(restrict)
                    }
                }
            },
        }
    }
}

impl FromIterator<Option<CaseMap>> for TransitionMap {
    fn from_iter<T: IntoIterator<Item = Option<CaseMap>>>(iter: T) -> Self {
        let mut result = TransitionMap::Tiny(Vec::new());

        for item in iter.into_iter() {
            result.push(item);
        }

        result
    }
}

impl TransitionMap {
    pub fn build<V: AsValue>(
        transitions: &[Transitions], inputs: &[V], requester: &mut impl Requester<CaseMap>,
    ) -> TransitionMap {
        transitions
            .iter()
            .map(|tr| tr.check_transition(inputs, requester))
            .collect::<TransitionMap>()
    }

    pub fn build_ext<V: AsValue>(
        transitions: &[Transitions], inputs: &[V], output: Option<CaseMap>, requester: &mut impl Requester<CaseMap>,
    ) -> TransitionMap {
        transitions
            .iter()
            .map(|tr| {
                if tr.0.is_empty() {
                    output
                } else {
                    tr.check_transition(inputs, requester)
                }
            })
            .collect::<TransitionMap>()
    }

    pub fn push_transition<V: AsValue>(
        &mut self, inputs: &[V], transition: &Transitions, requester: &mut impl Requester<CaseMap>,
    ) {
        self.push(transition.check_transition(inputs, requester))
    }

    pub fn remove_transitions(&mut self, transitions_to_remove: &GrowingBitmap) {
        let mut iter = transitions_to_remove.iter();

        match self {
            TransitionMap::Tiny(v) => v.retain_mut(|_| !iter.next().unwrap()),
            TransitionMap::Full(v) => v.retain_mut(|_| !iter.next().unwrap()),
        }
    }
}

impl fmt::Debug for TransitionMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        let mut first = true;
        for item in self.iter() {
            if !first {
                write!(f, " ")?;
            }

            first = false;

            match item {
                Some(m) => write!(f, "{m:?}")?,
                None => write!(f, "_")?,
            }
        }
        write!(f, "]")?;

        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Transition {
    pub input_index: usize,
    pub value: OwnedValue,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Transitions(Vec<Transition>);

impl FromIterator<Transition> for Transitions {
    fn from_iter<T: IntoIterator<Item = Transition>>(iter: T) -> Self {
        Transitions(iter.into_iter().collect())
    }
}

impl Transitions {
    pub fn from_vec(v: Vec<Transition>) -> Self {
        Transitions(v)
    }

    pub fn iter(&self) -> impl Iterator<Item = &Transition> + '_ {
        self.0.iter()
    }

    pub fn contains_input(&self, index: usize) -> bool {
        self.0.iter().any(|tr| tr.input_index == index)
    }

    pub fn check_transition<V: AsValue>(&self, inputs: &[V], requester: &mut impl Requester<CaseMap>) -> Option<CaseMap> {
        let mut m = inputs.iter().map(AsValue::as_value).collect::<ArrayVec<_, MAX_INPUTS>>();
        for transition in self.iter() {
            m[transition.input_index] = transition.value.as_value();
        }

        let result = requester.request(&m);
        debug!("{m:X?} -> {result:?}");

        result
    }
}
