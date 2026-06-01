use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::iter::once;

use liblisa::arch::Arch;
use liblisa::encoding::dataflows::{Dataflows, Dest, MemoryAccesses, Size, Source};
use liblisa::state::Location;
use liblisa::utils::bitmap::{DenseSet, GrowingBitmap};
use log::{debug, trace};

use super::{Change, ChangeLocation};

trait ContainsEx<T> {
    fn contains_ex<O>(&self, other: &O) -> bool
    where
        O: PartialEq<T>;
}

impl<T> ContainsEx<T> for &[T] {
    fn contains_ex<O>(&self, other: &O) -> bool
    where
        O: PartialEq<T>,
    {
        self.iter().any(|item| *other == *item)
    }
}

impl<T> ContainsEx<T> for Vec<T> {
    fn contains_ex<O>(&self, other: &O) -> bool
    where
        O: PartialEq<T>,
    {
        self.iter().any(|item| *other == *item)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum AnnotatedSource<A: Arch> {
    Source(Source<A>),
    Constant,
}

impl<A: Arch> AnnotatedSource<A> {
    fn size(&self) -> Option<Size> {
        match self {
            AnnotatedSource::Source(s) => s.size(),
            AnnotatedSource::Constant => None,
        }
    }

    fn source(&self) -> Option<&Source<A>> {
        match self {
            AnnotatedSource::Source(s) => Some(s),
            _ => None,
        }
    }

    fn overlaps_with(&self, other: &Dest<A>) -> bool {
        match self {
            AnnotatedSource::Source(Source::Dest(dest)) => dest.overlaps(other),
            _ => false,
        }
    }
}

impl<A: Arch> TryFrom<AnnotatedSource<A>> for Location<A> {
    type Error = ();

    fn try_from(value: AnnotatedSource<A>) -> Result<Self, Self::Error> {
        Location::try_from(&value)
    }
}

impl<'a, A: Arch> TryFrom<&'a AnnotatedSource<A>> for Location<A> {
    type Error = ();

    fn try_from(value: &'a AnnotatedSource<A>) -> Result<Self, Self::Error> {
        match value {
            AnnotatedSource::Source(s) => Ok(Location::try_from(s)?),
            AnnotatedSource::Constant => Err(()),
        }
    }
}

impl<A: Arch> TryFrom<AnnotatedSource<A>> for Dest<A> {
    type Error = ();

    fn try_from(value: AnnotatedSource<A>) -> Result<Self, Self::Error> {
        Dest::try_from(&value)
    }
}

impl<'a, A: Arch> TryFrom<&'a AnnotatedSource<A>> for Dest<A> {
    type Error = ();

    fn try_from(value: &'a AnnotatedSource<A>) -> Result<Self, Self::Error> {
        match value {
            AnnotatedSource::Source(s) => Ok(Dest::try_from(*s)?),
            AnnotatedSource::Constant => Err(()),
        }
    }
}

impl<A: Arch> PartialEq<Location<A>> for AnnotatedSource<A> {
    fn eq(&self, other: &Location<A>) -> bool {
        match (self, other) {
            (AnnotatedSource::Source(l), r) => l == r,
            _ => false,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum AnnotatedDest<A: Arch> {
    Dest(Dest<A>),
    Address(usize),
}

impl<A: Arch> AnnotatedDest<A> {
    fn size(&self) -> Option<Size> {
        match self {
            AnnotatedDest::Dest(s) => Some(s.size()),
            AnnotatedDest::Address(_) => None,
        }
    }

    fn overlaps_with(&self, other: &Dest<A>) -> bool {
        match (self, other) {
            (AnnotatedDest::Dest(a), b) => a.overlaps(b),
            _ => false,
        }
    }

    fn is_subset_of(&self, other: &Dest<A>) -> bool {
        match (self, other) {
            (AnnotatedDest::Dest(a), b) => {
                let loc_a = Location::from(a);
                let loc_b = Location::from(b);

                loc_a == loc_b && b.size().contains(&a.size())
            },
            _ => false,
        }
    }
}

impl<A: Arch> TryFrom<AnnotatedDest<A>> for Location<A> {
    type Error = ();

    fn try_from(value: AnnotatedDest<A>) -> Result<Self, Self::Error> {
        Location::try_from(&value)
    }
}

impl<'a, A: Arch> TryFrom<&'a AnnotatedDest<A>> for Location<A> {
    type Error = ();

    fn try_from(value: &'a AnnotatedDest<A>) -> Result<Self, Self::Error> {
        match value {
            AnnotatedDest::Dest(dest) => Ok(Location::from(dest)),
            AnnotatedDest::Address(_) => Err(()),
        }
    }
}

impl<A: Arch> TryFrom<AnnotatedDest<A>> for Dest<A> {
    type Error = ();

    fn try_from(value: AnnotatedDest<A>) -> Result<Self, Self::Error> {
        Dest::try_from(&value)
    }
}

impl<'a, A: Arch> TryFrom<&'a AnnotatedDest<A>> for Dest<A> {
    type Error = ();

    fn try_from(value: &'a AnnotatedDest<A>) -> Result<Self, Self::Error> {
        match value {
            AnnotatedDest::Dest(dest) => Ok(*dest),
            AnnotatedDest::Address(_) => Err(()),
        }
    }
}

impl<A: Arch> PartialEq<Location<A>> for AnnotatedDest<A> {
    fn eq(&self, other: &Location<A>) -> bool {
        match (self, other) {
            (AnnotatedDest::Dest(l), r) => l == r,
            _ => false,
        }
    }
}

#[derive(Clone, Debug)]
struct FlatDataflowWithLocation<A: Arch> {
    location: ChangeLocation,
    source: AnnotatedSource<A>,
    dest: AnnotatedDest<A>,
}

#[derive(Clone, Debug, PartialEq)]
struct FlatDataflow<A: Arch> {
    source: AnnotatedSource<A>,
    dest: AnnotatedDest<A>,
}

impl<A: Arch> PartialEq for FlatDataflowWithLocation<A> {
    fn eq(&self, other: &Self) -> bool {
        self.source == other.source && self.dest == other.dest
    }
}

impl<A: Arch> PartialEq<FlatDataflow<A>> for FlatDataflowWithLocation<A> {
    fn eq(&self, other: &FlatDataflow<A>) -> bool {
        self.source == other.source && self.dest == other.dest
    }
}

impl<A: Arch> PartialEq<FlatDataflowWithLocation<A>> for FlatDataflow<A> {
    fn eq(&self, other: &FlatDataflowWithLocation<A>) -> bool {
        self.source == other.source && self.dest == other.dest
    }
}

impl<A: Arch> From<FlatDataflowWithLocation<A>> for FlatDataflow<A> {
    fn from(value: FlatDataflowWithLocation<A>) -> Self {
        Self {
            source: value.source,
            dest: value.dest,
        }
    }
}

struct Dfs<'a, A: Arch> {
    all_added: &'a [FlatDataflow<A>],
    removed: &'a [FlatDataflowWithLocation<A>],
    retained: &'a [FlatDataflowWithLocation<A>],
    assignments: Vec<ChangeLocation>,
    paths: HashSet<Option<DataflowChange<A>>>,
    already_assigned: GrowingBitmap,
}

impl<'a, A: Arch> Dfs<'a, A> {
    fn any_retained_or_added(&self, mut pred: impl FnMut(&AnnotatedDest<A>, &AnnotatedSource<A>) -> bool) -> bool {
        self.retained
            .iter()
            .map(|x| (&x.dest, &x.source))
            .chain(self.all_added.iter().map(|x| (&x.dest, &x.source)))
            .any(|(dest, source)| pred(dest, source))
    }

    fn enumerate_folds(&mut self, num_not_assigned: usize, from: Option<&Location<A>>, to: Option<&Location<A>>) {
        if num_not_assigned > 4 {
            return
        }

        trace!("enumerate_folds({from:?}, {to:?}): {:?}", self.assignments);
        let num_pending = (0..self.removed.len())
            .filter(|&index| !self.already_assigned.get(index))
            .count()
            + num_not_assigned;
        trace!("num_pending={num_pending}");

        if num_pending <= 4 {
            let const_sources_pending = self
                .removed
                .iter()
                .enumerate()
                .filter(|&(index, _)| !self.already_assigned.get(index))
                .any(|(_, flow)| flow.source == AnnotatedSource::Constant);

            let can_ignore_pending = self
                .removed
                .iter()
                .enumerate()
                .filter(|&(index, _)| !self.already_assigned.get(index))
                .all(|(_, flow)| {
                    // Check if this dataflow was the only one to this destination that we had
                    let unique = self
                        .removed
                        .iter()
                        .chain(self.retained.iter())
                        .filter(|other| other.dest == flow.dest)
                        .count()
                        <= 1;

                    let identity = match &flow.source {
                        AnnotatedSource::Source(Source::Dest(d)) => flow.dest.overlaps_with(d),
                        _ => false,
                    };

                    !unique || identity
                });

            trace!("can_ignore_pending = {can_ignore_pending}");

            if !const_sources_pending && can_ignore_pending {
                let new = to.and_then(|to| {
                    from.map(|from| {
                        let mut change_locations = self.assignments.clone();
                        change_locations.sort();
                        change_locations.dedup();

                        DataflowChange {
                            change_locations,
                            from: *from,
                            to: *to,
                        }
                    })
                });

                if !self.paths.contains(&new) {
                    debug!("pushed: {new:?}");
                }

                self.paths.insert(new);

                trace!("self.paths.len() = {}", self.paths.len());
                trace!("num not assigned = {}", num_not_assigned);
            }
        }

        let mut checked_indices = Vec::new();
        let mut num_not_assigned = num_not_assigned;
        while let Some(removed_index) = (0..self.removed.len()).find(|&index| !self.already_assigned.get(index)) {
            if num_not_assigned > 4 {
                break
            }

            self.already_assigned.set(removed_index);
            checked_indices.push(removed_index);
            let item_from = &self.removed[removed_index];
            trace!("Trying to fold {item_from:?} with from={from:?} and to={to:?}");

            for match_target in self.retained.iter() {
                // Check A := B, .. changing into A := C, ..: source changed, destination equal
                if Self::size_contains(item_from.source.size(), match_target.source.size())
                    && Self::size_contains(item_from.dest.size(), match_target.dest.size())
                    && let Ok(from_loc) = Location::try_from(&item_from.source)
                    && let Ok(to_loc) = Location::try_from(&match_target.source)
                    && from_loc.matches_value_type_with(&to_loc)
                    && from.map(|from| &from_loc == from).unwrap_or(true)
                    && to.map(|to| &to_loc == to).unwrap_or(true)
                    && item_from.dest == match_target.dest
                {
                    trace!(
                        "Considering {:?}, .. -> {:?} changing into {:?}, .. -> {:?}",
                        item_from.source, item_from.dest, match_target.source, item_from.dest
                    );
                    self.assignments.push(item_from.location);
                    self.enumerate_folds(num_not_assigned, Some(&from_loc), Some(&to_loc));
                    self.assignments.pop();
                }
            }

            // Handle A := B, .. changing into A := 0, ..
            let zero_loc = Location::Reg(A::reg(A::ZERO));
            if to.map(|to| to == &zero_loc).unwrap_or(true)
                && let Ok(from_loc) = Location::try_from(&item_from.source)
                && from_loc.matches_value_type_with(&zero_loc)
                && from.map(|from| &from_loc == from).unwrap_or(true)
                && self.retained.iter().any(|flow| flow.dest == item_from.dest)
            {
                trace!(
                    "Considering {:?}, .. -> {:?} changing into 0, .. -> {:?}",
                    item_from.source, item_from.dest, item_from.dest
                );
                self.assignments.push(item_from.location);
                self.enumerate_folds(num_not_assigned, Some(&from_loc), Some(&zero_loc));
                self.assignments.pop();
            }

            // Handle A := id(B) changing into A := id(A)
            if let Ok(to_loc) = Location::try_from(&item_from.dest)
                && item_from.dest.size() == item_from.source.size()
                && to.map(|to| to == &to_loc).unwrap_or(true)
                && let Ok(from_loc) = Location::try_from(&item_from.source)
                && to_loc != from_loc
                && from_loc.matches_value_type_with(&to_loc)
                && from.map(|from| &from_loc == from).unwrap_or(true)
                && !self.removed.iter().any(|flow| {
                    flow != item_from
                        && flow.dest.overlaps_with(&Dest::try_from(&item_from.dest).unwrap())
                        && Location::try_from(&flow.source)
                            .ok()
                            .map(|loc| loc != to_loc)
                            .unwrap_or(false)
                })
                && !self.any_retained_or_added(|dest, _| {
                    *dest == to_loc && dest.overlaps_with(&Dest::try_from(&item_from.dest).unwrap())
                })
            {
                trace!(
                    "Considering id({:?}) -> {:?} changing into id({:?}) -> {:?}",
                    item_from.source, item_from.dest, to_loc, item_from.dest
                );

                for r in self.removed.iter().filter(|&flow| {
                    flow != item_from
                        && flow.dest.overlaps_with(&Dest::try_from(&item_from.dest).unwrap())
                        && Location::try_from(&flow.source)
                            .ok()
                            .map(|loc| loc != to_loc)
                            .unwrap_or(false)
                }) {
                    trace!("CONFLICT with {r:?}");
                }

                self.assignments.push(item_from.location);
                self.enumerate_folds(num_not_assigned, Some(&from_loc), Some(&to_loc));
                self.assignments.pop();
            }

            // Handle A := id(B), .. changing into B := id(B), ..
            // All others (..) must also be (parts of) B.
            if let Ok(to_loc) = Location::try_from(&item_from.source)
                && item_from.dest.size() == item_from.source.size()
                && to.map(|to| to == &to_loc).unwrap_or(true)
                && let Ok(from_loc) = Location::try_from(&item_from.dest)
                && to_loc != from_loc
                && from_loc.matches_value_type_with(&to_loc)
                && from.map(|from| &from_loc == from).unwrap_or(true)
                && !self.any_retained_or_added(|dest, _| {
                    *dest == to_loc && dest.overlaps_with(&Dest::try_from(&item_from.source).unwrap())
                })
                && !self.removed.iter().any(|flow| {
                    flow != item_from
                        && flow.dest.overlaps_with(&Dest::try_from(&item_from.dest).unwrap())
                        && flow.source != from_loc
                })
                && !self.any_retained_or_added(|dest, source| dest == &item_from.dest && *source != to_loc)
            {
                trace!(
                    "Considering id({:?}) -> {:?} changing into id({:?}) -> {:?}",
                    item_from.source, item_from.dest, item_from.source, to_loc
                );

                let len_before = self.assignments.len();
                for r in self.removed.iter().filter(|&flow| {
                    flow != item_from
                        && flow.dest.overlaps_with(&Dest::try_from(&item_from.dest).unwrap())
                        && !flow
                            .source
                            .overlaps_with(&Dest::from(to_loc).with_size(item_from.dest.size().unwrap_or(Size::qword())))
                }) {
                    trace!("Forcing {r:?} to change its source into {:?}", to_loc);
                    assert_eq!(r.source, from_loc);
                    self.assignments.push(r.location);
                }

                self.assignments.push(item_from.location.into_output());
                self.enumerate_folds(num_not_assigned, Some(&from_loc), Some(&to_loc));

                while self.assignments.len() > len_before {
                    self.assignments.pop();
                }
            }

            num_not_assigned += 1;
        }

        for index in checked_indices {
            self.already_assigned.reset(index);
        }
    }

    /// Returns true if both options contain a size and `added` is fully contained within or equal to `removed`
    fn size_contains(removed: Option<Size>, added: Option<Size>) -> bool {
        match (removed, added) {
            (Some(removed), Some(added)) => removed.contains(&added),
            (None, None) => true,
            _ => false,
        }
    }

    fn build_cases(&mut self, added: &[FlatDataflow<A>], from: Option<&Location<A>>, to: &Location<A>) {
        trace!("build_cases([{}], {from:?}, {to:?}): {:?}", added.len(), self.assignments);
        if added.is_empty() {
            self.enumerate_folds(0, from, Some(to));
        } else {
            let match_target = &added[0];
            let rest = &added[1..];

            trace!("Match target: {match_target:?}");

            for (index, removed_item) in self.removed.iter().enumerate() {
                // TODO: If the sizes aren't equal we need to merge all added sources that go to the full size destination and treat them as one.
                trace!("Considering removed item {index}: {removed_item:?}");
                let sizes_ok = Self::size_contains(removed_item.source.size(), match_target.source.size())
                    && Self::size_contains(removed_item.dest.size(), match_target.dest.size());
                // Handle A := B[0..1], C[2..3] changing into A := B[0..3] (= B[0..1], B[2..3])
                let matched_merged_source = if !sizes_ok
                    && Self::size_contains(match_target.source.size(), removed_item.source.size())
                    && Self::size_contains(removed_item.dest.size(), match_target.dest.size())
                    && let Some(full_size) = match_target.source.size()
                    && let Ok(source_loc) = Location::try_from(&match_target.source)
                {
                    let others = self
                        .removed
                        .iter()
                        .enumerate()
                        .filter(|&(i, _)| i != index)
                        .filter(|(_, item)| {
                            item.dest == removed_item.dest
                                && item.source == source_loc
                                && Self::size_contains(Some(full_size), item.source.size())
                        })
                        .collect::<Vec<_>>();
                    trace!("Others: {others:?}");
                    let mut bits_covered = DenseSet::new();
                    let removed_size = removed_item.source.size().unwrap();
                    for byte_index in removed_size.start_byte..=removed_size.end_byte {
                        bits_covered.set(byte_index);
                    }

                    let mut exactly_once = true;
                    for (_, other) in others.iter() {
                        let size = other.source.size().unwrap();
                        for byte_index in size.start_byte..=size.end_byte {
                            exactly_once &= bits_covered.set(byte_index);
                        }
                    }

                    if !exactly_once
                        || !(full_size.start_byte..=full_size.end_byte).all(|byte_index| bits_covered.contains(byte_index))
                    {
                        trace!("Not all bits covered or bits covered multiple times: {bits_covered:?}");
                        false
                    } else {
                        true
                    }
                } else {
                    false
                };
                if (sizes_ok || matched_merged_source) && self.already_assigned.set(index) {
                    let different_sized_dests = removed_item.dest.size() != match_target.dest.size();
                    let tmp;
                    let rest = if different_sized_dests {
                        let mut v = rest.to_vec();
                        v.retain(|x| {
                            if Location::try_from(&x.dest) == Location::try_from(&match_target.dest) {
                                let remove = Self::size_contains(removed_item.dest.size(), x.dest.size())
                                    && match_target.dest.size() != x.dest.size()
                                    && self.all_added.iter().any(|other| {
                                        Location::try_from(&other.dest) == Location::try_from(&x.dest)
                                            && other.dest.size() == match_target.dest.size()
                                            && other.source == x.source
                                    });

                                !remove
                            } else {
                                true
                            }
                        });

                        debug!("Constructed a new added: {v:?} with old item {removed_item:?}");

                        tmp = v;
                        &tmp
                    } else {
                        rest
                    };

                    // (_ -> A) and (location -> A): source changed, destination equal
                    if let Ok(source_loc) = Location::try_from(&removed_item.source)
                        && &match_target.source == to
                        && removed_item.dest == match_target.dest
                        && from.map(|loc| &removed_item.source == loc).unwrap_or(true)
                        && source_loc.matches_value_type_with(to)
                        && (source_loc != *to
                            || removed_item.source.size() != match_target.source.size()
                            || !self.paths.contains(&None))
                    {
                        trace!("Considering source change {source_loc:?} -> {to:?}");
                        if &source_loc == to {
                            self.build_cases(rest, from, to);
                        } else {
                            self.assignments.push(removed_item.location);
                            self.build_cases(rest, Some(&source_loc), to);
                            self.assignments.pop();
                        }
                    }

                    // (A -> _) and (A -> location): source equal, destination changed
                    if let Ok(dest_loc) = Location::try_from(&removed_item.dest)
                        && &match_target.dest == to
                        && removed_item.source == match_target.source
                        && from.map(|loc| &removed_item.dest == loc).unwrap_or(true)
                        && dest_loc.matches_value_type_with(to)
                        && !self
                            .retained
                            .iter()
                            .chain(self.removed.iter().filter(|_| !different_sized_dests))
                            .any(|flow| {
                                flow.dest == *to
                                    && flow
                                        .dest
                                        .overlaps_with(&Dest::from(*to).with_size(removed_item.dest.size().unwrap()))
                            })
                    {
                        trace!("Considering destination change {dest_loc:?} -> {to:?}");
                        if &dest_loc == to {
                            self.build_cases(rest, from, to);
                        } else {
                            self.assignments.push(removed_item.location.into_output());
                            self.build_cases(rest, Some(&dest_loc), to);
                            self.assignments.pop();
                        }
                    }

                    // (_ -> _) and (location -> location): both changed
                    if let Ok(source_loc) = Location::try_from(&removed_item.source)
                        && let Ok(dest_loc) = Location::try_from(&removed_item.dest)
                        && &match_target.source == to
                        && &match_target.dest == to
                        && source_loc == dest_loc
                        && from.map(|loc| &removed_item.dest == loc).unwrap_or(true)
                        && dest_loc.matches_value_type_with(to)
                    {
                        trace!("Considering source and destination change {dest_loc:?} -> {to:?}");
                        if &dest_loc == to {
                            self.build_cases(rest, from, to);
                        } else {
                            self.assignments.push(removed_item.location);
                            self.assignments.push(removed_item.location.into_output());
                            self.build_cases(rest, Some(&dest_loc), to);
                            self.assignments.pop();
                            self.assignments.pop();
                        }
                    }

                    self.already_assigned.reset(index);
                }
            }
        }
    }

    pub fn search(
        tos: impl Iterator<Item = Location<A>>, removed: &'a [FlatDataflowWithLocation<A>], added: &[FlatDataflow<A>],
        retained: &[FlatDataflowWithLocation<A>],
    ) -> Vec<Option<DataflowChange<A>>> {
        let mut dfs = Dfs {
            all_added: added,
            removed,
            retained,
            assignments: Vec::new(),
            paths: HashSet::new(),
            already_assigned: GrowingBitmap::new(),
        };

        if added.iter().all(|item| item.source == AnnotatedSource::Constant) {
            dfs.enumerate_folds(0, None, None);
        }

        for to in tos {
            dfs.build_cases(added, None, &to);
        }

        let mut v = dfs.paths.drain().collect::<Vec<_>>();
        v.sort();
        v.dedup();

        v
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct DataflowChange<A: Arch> {
    pub from: Location<A>,
    pub to: Location<A>,
    pub change_locations: Vec<ChangeLocation>,
}

impl<A: Arch> DataflowChange<A> {
    fn dests_from_dataflow(flow: &FlatDataflow<A>) -> impl Iterator<Item = Location<A>> {
        once(Dest::try_from(flow.source.clone()))
            .flatten()
            .map(Location::from)
            .chain(once(Location::try_from(flow.dest.clone())).flatten())
    }

    fn compute_shared_locations(items: &[FlatDataflow<A>]) -> Vec<Location<A>> {
        if items.is_empty() {
            Vec::new()
        } else {
            let mut dests = Self::dests_from_dataflow(&items[0]).collect::<Vec<_>>();
            dests.dedup();

            for item in items.iter() {
                let new_dests = Self::dests_from_dataflow(item).collect::<Vec<_>>();
                dests.retain(|dest| new_dests.contains(dest));
            }

            dests
        }
    }

    fn compare(old: &[FlatDataflowWithLocation<A>], new: &[FlatDataflow<A>]) -> Vec<Option<DataflowChange<A>>> {
        let removed = old.iter().filter(|&item| !new.contains_ex(item)).cloned().collect::<Vec<_>>();

        debug!("Adjusting new = {new:?}");
        // Adjust added so that if removed contains a destination that ended up being split in added, we re-merge them.
        // For example: if removed = [A[0..3] <- ...], added = [A[0..1] <- ..., A[2..3] <- ..], then we want to merge A[0..1] and A[2..3] in added.
        let old_dests = removed
            .iter()
            .flat_map(|r| match &r.dest {
                AnnotatedDest::Dest(d) => Some(*d),
                AnnotatedDest::Address(_) => None,
            })
            .collect::<HashSet<_>>();

        // First we expand all the dests to match the original dests
        let mut new = new.to_vec();
        for new_flow in new.iter_mut() {
            if let Some(removed_dest) = old_dests.iter().find(|d| new_flow.dest.is_subset_of(d)) {
                new_flow.dest = AnnotatedDest::Dest(*removed_dest);
            }
        }

        debug!("Expanded dests = {new:?}");

        // Next we merge sources when they go to the same dest
        let new = {
            let mut groups = HashMap::new();
            let mut untouched = Vec::new();

            for added_flow in new.drain(..) {
                let location = match &added_flow.source {
                    AnnotatedSource::Source(s) => Location::try_from(s).ok(),
                    AnnotatedSource::Constant => None,
                };

                if let Some(location) = location
                    && !location.is_flags()
                {
                    groups
                        .entry((added_flow.dest.clone(), location))
                        .or_insert_with(Vec::new)
                        .push(added_flow);
                } else {
                    untouched.push(added_flow);
                }
            }

            new.extend(untouched);

            for ((dest, _), group) in groups {
                debug!("Merging {group:?}");
                let start_byte = group
                    .iter()
                    .map(|m| m.source.source().unwrap().size().map(|s| s.start_byte))
                    .fold(None, |a, b| match (a, b) {
                        (None, None) => None,
                        (None, Some(b)) => Some(b),
                        (Some(a), None) => Some(a),
                        (Some(a), Some(b)) => Some(a.min(b)),
                    });
                let end_byte = group
                    .iter()
                    .map(|m| m.source.source().unwrap().size().map(|s| s.end_byte))
                    .fold(None, |a, b| match (a, b) {
                        (None, None) => None,
                        (None, Some(b)) => Some(b),
                        (Some(a), None) => Some(a),
                        (Some(a), Some(b)) => Some(a.max(b)),
                    });
                debug!("start_byte={start_byte:?}, end_byte={end_byte:?}");
                new.push(FlatDataflow {
                    dest,
                    source: AnnotatedSource::Source(
                        group[0]
                            .source
                            .source()
                            .unwrap()
                            .with_size(Size::new(start_byte.unwrap_or(0), end_byte.unwrap_or(0))),
                    ),
                });
            }

            new
        };

        debug!("Adjusted new = {new:?}");

        let removed = old.iter().filter(|&item| !new.contains_ex(item)).cloned().collect::<Vec<_>>();
        let added = new.iter().filter(|&item| !old.contains_ex(item)).cloned().collect::<Vec<_>>();
        let retained = old.iter().filter(|&item| new.contains_ex(item)).cloned().collect::<Vec<_>>();

        debug!("Removed = {removed:?}");
        debug!("Added = {added:?}");

        let shared_added = Self::compute_shared_locations(&added);
        debug!("Shared locations: {:?}", shared_added);

        if shared_added.is_empty() && !added.is_empty() {
            debug!("Comparison invalid: could not find a shared dest");
            return Vec::new();
        }

        let all_assignments = Dfs::search(shared_added.iter().cloned(), &removed, &added, &retained);
        debug!("All possible assignments ({}): {all_assignments:?}", all_assignments.len());
        all_assignments
    }

    fn flatten_accesses<T: From<FlatDataflowWithLocation<A>>>(accesses: &MemoryAccesses<A>) -> Vec<T> {
        let mut result = Vec::new();
        for (memory_index, flow) in accesses.memory.iter().enumerate() {
            if flow.inputs.is_empty() {
                result.push(
                    FlatDataflowWithLocation {
                        location: ChangeLocation::MemoryAddress {
                            memory_index,
                            input_index: 0,
                        },
                        source: AnnotatedSource::Constant,
                        dest: AnnotatedDest::Address(memory_index),
                    }
                    .into(),
                );
            }

            for (source_index, source) in flow.inputs().iter().enumerate() {
                result.push(
                    FlatDataflowWithLocation {
                        location: ChangeLocation::MemoryAddress {
                            memory_index,
                            input_index: source_index,
                        },
                        source: AnnotatedSource::Source(*source),
                        dest: AnnotatedDest::Address(memory_index),
                    }
                    .into(),
                );
            }
        }

        result
    }

    pub fn compare_memory_accesses(
        old_accesses: &MemoryAccesses<A>, new_accesses: &MemoryAccesses<A>,
    ) -> Vec<Option<DataflowChange<A>>> {
        if old_accesses.len() != new_accesses.len()
            || old_accesses
                .memory
                .iter()
                .zip(new_accesses.memory.iter())
                .any(|(old, new)| old.alignment != new.alignment || old.kind != new.kind)
        {
            Vec::new()
        } else {
            let old_accesses = Self::flatten_accesses(old_accesses);
            let new_accesses = Self::flatten_accesses(new_accesses);

            Self::compare(&old_accesses, &new_accesses)
        }
    }

    fn flatten_dataflows<T: From<FlatDataflowWithLocation<A>>>(dataflows: &Dataflows<A, ()>) -> Vec<T> {
        let mut result = Vec::new();
        for (output_index, flow) in dataflows.output_dataflows().enumerate() {
            if flow.inputs.is_empty() {
                result.push(
                    FlatDataflowWithLocation {
                        location: ChangeLocation::InputForOutput {
                            output_index,
                            input_index: 0,
                        },
                        source: AnnotatedSource::Constant,
                        dest: AnnotatedDest::Dest(flow.target),
                    }
                    .into(),
                );
            }

            for (source_index, source) in flow.inputs().iter().enumerate() {
                result.push(
                    FlatDataflowWithLocation {
                        location: ChangeLocation::InputForOutput {
                            output_index,
                            input_index: source_index,
                        },
                        source: AnnotatedSource::Source(*source),
                        dest: AnnotatedDest::Dest(flow.target),
                    }
                    .into(),
                );
            }
        }

        result
    }

    pub fn compare_dataflows(
        old_dataflows: &Dataflows<A, ()>, new_dataflows: &Dataflows<A, ()>,
    ) -> Vec<Option<DataflowChange<A>>> {
        let old_dataflows = Self::flatten_dataflows(old_dataflows);
        let new_dataflows = Self::flatten_dataflows(new_dataflows);

        Self::compare(&old_dataflows, &new_dataflows)
    }

    pub fn into_change(changes: Vec<Option<DataflowChange<A>>>) -> Change<A> {
        let num = changes.len();
        let mut change = Change::Multiple(
            changes
                .into_iter()
                .flat_map(|change| match change {
                    None => {
                        if num > 1 {
                            None
                        } else {
                            Some(Change::None)
                        }
                    },
                    Some(change) => {
                        if let Location::Reg(from) = change.from
                            && let Location::Reg(to) = change.to
                        {
                            Some(Change::Register {
                                from,
                                to,
                                locations: change.change_locations,
                            })
                        } else {
                            None
                        }
                    },
                })
                .collect(),
        );
        change.normalize();
        change
    }
}

#[cfg(test)]
mod tests {
    use liblisa::arch::fake::{FakeArch, FakeReg};
    use liblisa::encoding::dataflows::{
        AccessKind, AddressComputation, Dataflow, Dataflows, Dest, Inputs, MemoryAccess, MemoryAccesses, Size, Source,
    };
    use liblisa::instr::Instruction;
    use liblisa::state::Location;
    use test_log::test;

    use super::{ChangeLocation, DataflowChange};

    #[test]
    pub fn diff_memory_accesses() {
        let a = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        assert_eq!(DataflowChange::compare_memory_accesses(&a, &a), vec![None]);

        let a2 = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: vec![MemoryAccess {
                inputs: Inputs::sorted(Vec::new()),
                alignment: 1,
                calculation: AddressComputation::unscaled_sum(0),
                kind: AccessKind::Executable,
                size: 4..4,
            }],
            use_trap_flag: false,
        };
        assert_eq!(DataflowChange::compare_memory_accesses(&a, &a2), vec![]);
        assert_eq!(DataflowChange::compare_memory_accesses(&a2, &a), vec![]);

        let a2b = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: vec![MemoryAccess {
                inputs: Inputs::sorted(Vec::new()),
                alignment: 4,
                calculation: AddressComputation::unscaled_sum(0),
                kind: AccessKind::Executable,
                size: 4..4,
            }],
            use_trap_flag: false,
        };
        assert_eq!(DataflowChange::compare_memory_accesses(&a2, &a2b), vec![]);
        assert_eq!(DataflowChange::compare_memory_accesses(&a2b, &a2), vec![]);

        let a2c = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: vec![MemoryAccess {
                inputs: Inputs::sorted(Vec::new()),
                alignment: 1,
                calculation: AddressComputation::unscaled_sum(0),
                kind: AccessKind::Input,
                size: 4..4,
            }],
            use_trap_flag: false,
        };
        assert_eq!(DataflowChange::compare_memory_accesses(&a2, &a2c), vec![]);
        assert_eq!(DataflowChange::compare_memory_accesses(&a2c, &a2), vec![]);

        let a3 = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: vec![MemoryAccess {
                inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                alignment: 1,
                calculation: AddressComputation::unscaled_sum(0),
                kind: AccessKind::Executable,
                size: 4..4,
            }],
            use_trap_flag: false,
        };
        assert_eq!(DataflowChange::compare_memory_accesses(&a3, &a2), vec![]);
        assert_eq!(DataflowChange::compare_memory_accesses(&a3, &a3), vec![None]);

        let a4 = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: vec![MemoryAccess {
                inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R2, Size::qword()))]),
                alignment: 1,
                calculation: AddressComputation::unscaled_sum(0),
                kind: AccessKind::Executable,
                size: 4..4,
            }],
            use_trap_flag: false,
        };
        assert_eq!(
            DataflowChange::compare_memory_accesses(&a4, &a3),
            vec![Some(DataflowChange {
                from: Location::Reg(FakeReg::R2),
                to: Location::Reg(FakeReg::R0),
                change_locations: vec![ChangeLocation::MemoryAddress {
                    memory_index: 0,
                    input_index: 0
                },],
            })]
        );
    }

    #[test]
    pub fn diff_identical() {
        let d = Dataflows {
            addresses: MemoryAccesses::<FakeArch> {
                instr: Instruction::new(&[]),
                memory: Vec::new(),
                use_trap_flag: false,
            },
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R2, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R2, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        assert_eq!(DataflowChange::compare_dataflows(&d, &d), vec![None]);
    }

    #[test]
    pub fn diff_resize() {
        let d1 = Dataflows {
            addresses: MemoryAccesses::<FakeArch> {
                instr: Instruction::new(&[]),
                memory: Vec::new(),
                use_trap_flag: false,
            },
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R0, Size::qword()),
                inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: MemoryAccesses::<FakeArch> {
                instr: Instruction::new(&[]),
                memory: Vec::new(),
                use_trap_flag: false,
            },
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R0, Size::new(1, 6)),
                inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        assert_eq!(DataflowChange::compare_dataflows(&d1, &d2), vec![None]);
    }

    #[test]
    pub fn diff_one_split() {
        let d1 = Dataflows {
            addresses: MemoryAccesses::<FakeArch> {
                instr: Instruction::new(&[]),
                memory: Vec::new(),
                use_trap_flag: false,
            },
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R0, Size::new(0, 15)),
                inputs: Inputs::sorted(vec![
                    Source::Dest(Dest::Reg(FakeReg::R0, Size::qword())),
                    Source::Dest(Dest::Reg(FakeReg::R1, Size::qword())),
                ]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: MemoryAccesses::<FakeArch> {
                instr: Instruction::new(&[]),
                memory: Vec::new(),
                use_trap_flag: false,
            },
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::new(0, 12)),
                    inputs: Inputs::sorted(vec![
                        Source::Dest(Dest::Reg(FakeReg::R0, Size::qword())),
                        Source::Dest(Dest::Reg(FakeReg::R1, Size::qword())),
                    ]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::new(13, 13)),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R1, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::new(14, 15)),
                    inputs: Inputs::sorted(vec![
                        Source::Dest(Dest::Reg(FakeReg::R0, Size::qword())),
                        Source::Dest(Dest::Reg(FakeReg::R1, Size::qword())),
                    ]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        assert_eq!(DataflowChange::compare_dataflows(&d1, &d2), vec![None]);
    }

    #[test]
    pub fn diff_single_change() {
        let a = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R2, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R2, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a.clone(),
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R3, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R2, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        assert_eq!(
            DataflowChange::compare_dataflows(&d1, &d2),
            vec![Some(DataflowChange {
                from: Location::Reg(FakeReg::R2),
                to: Location::Reg(FakeReg::R3),
                change_locations: vec![ChangeLocation::Output(1),],
            })]
        );

        let d2 = Dataflows {
            addresses: a,
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R3, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R3, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        assert_eq!(
            DataflowChange::compare_dataflows(&d1, &d2),
            vec![Some(DataflowChange {
                from: Location::Reg(FakeReg::R2),
                to: Location::Reg(FakeReg::R3),
                change_locations: vec![
                    ChangeLocation::Output(1),
                    ChangeLocation::InputForOutput {
                        output_index: 1,
                        input_index: 0
                    },
                ],
            })]
        );
    }

    #[test]
    pub fn diff_size_subset() {
        let a = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R2, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R2, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a.clone(),
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R2, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R2, Size::new(0, 5)))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        assert_eq!(DataflowChange::compare_dataflows(&d1, &d2), vec![None]);

        let d2 = Dataflows {
            addresses: a,
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R2, Size::new(0, 6)),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R2, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        assert_eq!(DataflowChange::compare_dataflows(&d1, &d2), vec![None]);
    }

    #[test]
    pub fn diff_items_left_out() {
        let a = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R2, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R2, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a.clone(),
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R0, Size::qword()),
                inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        assert_eq!(DataflowChange::compare_dataflows(&d1, &d2), vec![None,]);

        let d2 = Dataflows {
            addresses: a,
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R2, Size::qword()),
                    inputs: Inputs::sorted(vec![]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        assert_eq!(DataflowChange::compare_dataflows(&d1, &d2), vec![None]);
    }

    #[test]
    pub fn diff_invalid_items_left_out() {
        let a = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R0, Size::qword()),
                inputs: Inputs::sorted(vec![Source::Dest(Dest::Mem(0, Size::qword()))]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a,
            outputs: vec![],
            found_dependent_bytes: false,
        };
        assert_eq!(DataflowChange::compare_dataflows(&d1, &d2), vec![]);
    }

    #[test]
    pub fn diff_two_possibilities() {
        let a = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R2, Size::qword()),
                    inputs: Inputs::sorted(vec![
                        Source::Dest(Dest::Reg(FakeReg::R2, Size::new(4, 4))),
                        Source::Dest(Dest::Reg(FakeReg::R3, Size::qword())),
                    ]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R4, Size::qword()),
                    inputs: Inputs::sorted(vec![
                        Source::Dest(Dest::Reg(FakeReg::R4, Size::new(4, 4))),
                        Source::Dest(Dest::Reg(FakeReg::R3, Size::qword())),
                    ]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a,
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R6, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R3, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        assert_eq!(
            DataflowChange::compare_dataflows(&d1, &d2),
            vec![
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R2),
                    to: Location::Reg(FakeReg::R6),
                    change_locations: vec![ChangeLocation::Output(1),],
                }),
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R4),
                    to: Location::Reg(FakeReg::R6),
                    change_locations: vec![ChangeLocation::Output(2),],
                }),
            ]
        );
    }

    #[test]
    pub fn diff_fold() {
        let a = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R2, Size::qword()),
                inputs: Inputs::sorted(vec![
                    Source::Dest(Dest::Reg(FakeReg::R3, Size::qword())),
                    Source::Dest(Dest::Reg(FakeReg::R4, Size::qword())),
                ]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a,
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R2, Size::qword()),
                inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R3, Size::qword()))]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        assert_eq!(
            DataflowChange::compare_dataflows(&d1, &d2),
            vec![
                None,
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R4),
                    to: Location::Reg(FakeReg::R3),
                    change_locations: vec![ChangeLocation::InputForOutput {
                        output_index: 0,
                        input_index: 1
                    },],
                }),
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R4),
                    to: Location::Reg(FakeReg::RZ),
                    change_locations: vec![ChangeLocation::InputForOutput {
                        output_index: 0,
                        input_index: 1
                    },],
                }),
            ]
        );
    }

    #[test]
    pub fn diff_invalid_fold() {
        let a = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R2, Size::qword()),
                inputs: Inputs::sorted(vec![
                    Source::Dest(Dest::Reg(FakeReg::R3, Size::qword())),
                    Source::Dest(Dest::Reg(FakeReg::R4, Size::qword())),
                ]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a,
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R2, Size::qword()),
                inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R5, Size::qword()))]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        assert_eq!(
            DataflowChange::compare_dataflows(&d1, &d2),
            vec![
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R3),
                    to: Location::Reg(FakeReg::R5),
                    change_locations: vec![ChangeLocation::InputForOutput {
                        output_index: 0,
                        input_index: 0
                    },],
                }),
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R4),
                    to: Location::Reg(FakeReg::R5),
                    change_locations: vec![ChangeLocation::InputForOutput {
                        output_index: 0,
                        input_index: 1
                    },],
                }),
            ]
        );
    }

    #[test]
    pub fn diff_double_fold() {
        let a = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R2, Size::qword()),
                    inputs: Inputs::sorted(vec![
                        Source::Dest(Dest::Reg(FakeReg::R2, Size::qword())),
                        Source::Dest(Dest::Reg(FakeReg::R3, Size::qword())),
                    ]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::RF, Size::qword()),
                    inputs: Inputs::sorted(vec![
                        Source::Dest(Dest::Reg(FakeReg::R2, Size::qword())),
                        Source::Dest(Dest::Reg(FakeReg::R3, Size::qword())),
                    ]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a,
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R3, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R3, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::RF, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R3, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };

        assert_eq!(
            DataflowChange::compare_dataflows(&d1, &d2),
            vec![
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R2),
                    to: Location::Reg(FakeReg::R3),
                    change_locations: vec![ChangeLocation::Output(0),],
                }),
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R2),
                    to: Location::Reg(FakeReg::R3),
                    change_locations: vec![
                        ChangeLocation::Output(0),
                        ChangeLocation::InputForOutput {
                            output_index: 0,
                            input_index: 0
                        },
                    ],
                }),
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R2),
                    to: Location::Reg(FakeReg::R3),
                    change_locations: vec![
                        ChangeLocation::Output(0),
                        ChangeLocation::InputForOutput {
                            output_index: 0,
                            input_index: 0
                        },
                        ChangeLocation::InputForOutput {
                            output_index: 1,
                            input_index: 0
                        },
                    ],
                }),
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R2),
                    to: Location::Reg(FakeReg::R3),
                    change_locations: vec![
                        ChangeLocation::Output(0),
                        ChangeLocation::InputForOutput {
                            output_index: 1,
                            input_index: 0
                        },
                    ],
                }),
            ]
        );
    }

    #[test]
    pub fn diff_empty_sources() {
        let a = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R2, Size::qword()),
                inputs: Inputs::sorted(vec![]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a.clone(),
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R3, Size::qword()),
                inputs: Inputs::sorted(vec![]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        assert_eq!(
            DataflowChange::compare_dataflows(&d1, &d2),
            vec![Some(DataflowChange {
                from: Location::Reg(FakeReg::R2),
                to: Location::Reg(FakeReg::R3),
                change_locations: vec![ChangeLocation::Output(0),],
            }),]
        );

        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R2, Size::qword()),
                    inputs: Inputs::sorted(vec![]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R4, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R4, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a,
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R3, Size::qword()),
                inputs: Inputs::sorted(vec![]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        assert_eq!(
            DataflowChange::compare_dataflows(&d1, &d2),
            vec![Some(DataflowChange {
                from: Location::Reg(FakeReg::R2),
                to: Location::Reg(FakeReg::R3),
                change_locations: vec![ChangeLocation::Output(0),],
            }),]
        );
    }

    /// Empty sources imply a constant value is being assigned to the destination.
    /// We can *always* detect this, so it would make no sense if it disappears.
    /// Therefore it must always be considered an error.
    #[test]
    pub fn diff_empty_sources_cannot_be_removed() {
        let a = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R2, Size::qword()),
                inputs: Inputs::sorted(vec![]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a,
            outputs: vec![],
            found_dependent_bytes: false,
        };

        assert_eq!(DataflowChange::compare_dataflows(&d1, &d2), vec![]);
    }

    #[test]
    pub fn diff_identity_source_changed_other_reg() {
        let a = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R2, Size::qword()),
                inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R3, Size::qword()))]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a,
            outputs: vec![],
            found_dependent_bytes: false,
        };
        assert_eq!(
            DataflowChange::compare_dataflows(&d1, &d2),
            vec![
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R2),
                    to: Location::Reg(FakeReg::R3),
                    change_locations: vec![ChangeLocation::Output(0),],
                }),
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R3),
                    to: Location::Reg(FakeReg::R2),
                    change_locations: vec![ChangeLocation::InputForOutput {
                        output_index: 0,
                        input_index: 0
                    },],
                }),
            ]
        );

        let a = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R2, Size::qword()),
                inputs: Inputs::sorted(vec![
                    Source::Dest(Dest::Reg(FakeReg::R2, Size::new(0, 1))),
                    Source::Dest(Dest::Reg(FakeReg::R3, Size::qword())),
                ]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a,
            outputs: vec![],
            found_dependent_bytes: false,
        };
        assert_eq!(
            DataflowChange::compare_dataflows(&d1, &d2),
            vec![
                None,
                // Changing R2 to R3 only makes sense if we get all sources and the destination to R3.
                // We cannot leave R2 in the sources, because we would have seen that...
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R2),
                    to: Location::Reg(FakeReg::R3),
                    change_locations: vec![
                        ChangeLocation::Output(0),
                        ChangeLocation::InputForOutput {
                            output_index: 0,
                            input_index: 0
                        },
                    ],
                }),
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R3),
                    to: Location::Reg(FakeReg::R2),
                    change_locations: vec![ChangeLocation::InputForOutput {
                        output_index: 0,
                        input_index: 1
                    },],
                }),
            ]
        );
    }

    #[test]
    pub fn diff_identity_source_changed_same_reg() {
        let a = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R2, Size::new(0, 3)),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R3, Size::new(0, 3)))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R2, Size::new(4, 7)),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R7, Size::new(0, 3)))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a.clone(),
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R2, Size::new(4, 7)),
                inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R7, Size::new(0, 3)))]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        assert_eq!(
            DataflowChange::compare_dataflows(&d1, &d2),
            vec![
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R2),
                    to: Location::Reg(FakeReg::R3),
                    change_locations: vec![ChangeLocation::Output(0),],
                }),
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R3),
                    to: Location::Reg(FakeReg::R2),
                    change_locations: vec![ChangeLocation::InputForOutput {
                        output_index: 0,
                        input_index: 0
                    },],
                }),
            ]
        );

        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R2, Size::new(0, 3)),
                    inputs: Inputs::sorted(vec![
                        Source::Dest(Dest::Reg(FakeReg::R2, Size::new(0, 0))),
                        Source::Dest(Dest::Reg(FakeReg::R3, Size::new(0, 3))),
                    ]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R2, Size::new(4, 7)),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R7, Size::new(0, 3)))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a,
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R2, Size::new(4, 7)),
                inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R7, Size::new(0, 3)))]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        assert_eq!(
            DataflowChange::compare_dataflows(&d1, &d2),
            vec![
                None,
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R2),
                    to: Location::Reg(FakeReg::R3),
                    change_locations: vec![
                        ChangeLocation::Output(0),
                        ChangeLocation::InputForOutput {
                            output_index: 0,
                            input_index: 0
                        },
                    ],
                }),
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R3),
                    to: Location::Reg(FakeReg::R2),
                    change_locations: vec![ChangeLocation::InputForOutput {
                        output_index: 0,
                        input_index: 1
                    },],
                }),
            ]
        );
    }

    #[test]
    pub fn diff_identity_dest_only() {
        let a = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R2, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R3, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R5, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R2, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a.clone(),
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R5, Size::qword()),
                inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R3, Size::qword()))]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        assert_eq!(
            DataflowChange::compare_dataflows(&d1, &d2),
            vec![Some(DataflowChange {
                from: Location::Reg(FakeReg::R2),
                to: Location::Reg(FakeReg::R3),
                change_locations: vec![
                    ChangeLocation::Output(0),
                    ChangeLocation::InputForOutput {
                        output_index: 1,
                        input_index: 0
                    },
                ],
            }),]
        );

        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R2, Size::qword()),
                    inputs: Inputs::sorted(vec![
                        Source::Dest(Dest::Reg(FakeReg::R2, Size::qword())),
                        Source::Dest(Dest::Reg(FakeReg::R3, Size::qword())),
                    ]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R5, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R2, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a,
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R5, Size::qword()),
                inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R3, Size::qword()))]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        assert_eq!(
            DataflowChange::compare_dataflows(&d1, &d2),
            vec![
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R2),
                    to: Location::Reg(FakeReg::R3),
                    change_locations: vec![
                        ChangeLocation::Output(0),
                        ChangeLocation::InputForOutput {
                            output_index: 0,
                            input_index: 0
                        },
                        ChangeLocation::InputForOutput {
                            output_index: 1,
                            input_index: 0
                        },
                    ],
                }),
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R2),
                    to: Location::Reg(FakeReg::R3),
                    change_locations: vec![ChangeLocation::InputForOutput {
                        output_index: 1,
                        input_index: 0
                    },],
                }),
            ]
        );
    }

    #[test]
    pub fn diff_merged_source1() {
        let a = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R0, Size::qword()),
                inputs: Inputs::sorted(vec![
                    Source::Dest(Dest::Reg(FakeReg::R1, Size::new(0, 1))),
                    Source::Dest(Dest::Reg(FakeReg::R2, Size::new(2, 3))),
                ]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a,
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R0, Size::qword()),
                inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R2, Size::new(0, 3)))]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        assert_eq!(
            DataflowChange::compare_dataflows(&d1, &d2),
            vec![Some(DataflowChange {
                from: Location::Reg(FakeReg::R1),
                to: Location::Reg(FakeReg::R2),
                change_locations: vec![ChangeLocation::InputForOutput {
                    output_index: 0,
                    input_index: 0
                },],
            }),]
        );
    }

    #[test]
    pub fn diff_merged_source2() {
        let a = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R0, Size::qword()),
                inputs: Inputs::sorted(vec![
                    Source::Dest(Dest::Reg(FakeReg::R1, Size::new(0, 1))),
                    Source::Dest(Dest::Reg(FakeReg::R2, Size::new(2, 3))),
                ]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a,
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R0, Size::qword()),
                inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R1, Size::new(0, 3)))]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        assert_eq!(
            DataflowChange::compare_dataflows(&d1, &d2),
            vec![Some(DataflowChange {
                from: Location::Reg(FakeReg::R2),
                to: Location::Reg(FakeReg::R1),
                change_locations: vec![ChangeLocation::InputForOutput {
                    output_index: 0,
                    input_index: 1
                },],
            }),]
        );
    }

    #[test]
    pub fn diff_merged_source_multiple() {
        let a = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R0, Size::qword()),
                inputs: Inputs::sorted(vec![
                    Source::Dest(Dest::Reg(FakeReg::R1, Size::new(0, 1))),
                    Source::Dest(Dest::Reg(FakeReg::R2, Size::new(2, 3))),
                    Source::Dest(Dest::Reg(FakeReg::R3, Size::qword())),
                ]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a,
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R0, Size::qword()),
                inputs: Inputs::sorted(vec![
                    Source::Dest(Dest::Reg(FakeReg::R1, Size::new(0, 3))),
                    Source::Dest(Dest::Reg(FakeReg::R3, Size::qword())),
                ]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        assert_eq!(
            DataflowChange::compare_dataflows(&d1, &d2),
            vec![Some(DataflowChange {
                from: Location::Reg(FakeReg::R2),
                to: Location::Reg(FakeReg::R1),
                change_locations: vec![ChangeLocation::InputForOutput {
                    output_index: 0,
                    input_index: 1
                },],
            }),]
        );
    }

    #[test]
    pub fn diff_different_register_types() {
        // Merged source
        let a = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R0, Size::qword()),
                inputs: Inputs::sorted(vec![
                    Source::Dest(Dest::Reg(FakeReg::B0, Size::new(0, 1))),
                    Source::Dest(Dest::Reg(FakeReg::R2, Size::new(2, 3))),
                ]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a,
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R0, Size::qword()),
                inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R2, Size::new(0, 3)))]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        assert_eq!(DataflowChange::compare_dataflows(&d1, &d2), vec![]);

        // Single changes
        let a = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R2, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R2, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a.clone(),
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::B0, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R2, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        assert_eq!(DataflowChange::compare_dataflows(&d1, &d2), vec![]);

        let d2 = Dataflows {
            addresses: a,
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R0, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::B0, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::B0, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        assert_eq!(DataflowChange::compare_dataflows(&d1, &d2), vec![]);

        // Identity dest
        let a = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::B0, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::B0, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R5, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R2, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a,
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R5, Size::qword()),
                inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R3, Size::qword()))]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        assert_eq!(
            DataflowChange::compare_dataflows(&d1, &d2),
            vec![Some(DataflowChange {
                from: Location::Reg(FakeReg::R2),
                to: Location::Reg(FakeReg::R3),
                change_locations: vec![ChangeLocation::InputForOutput {
                    output_index: 1,
                    input_index: 0
                },],
            }),]
        );
    }

    #[test]
    pub fn diff_many_outputs_changed() {
        // Merged source
        let a = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: (0..16)
                .map(|n| Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::new(n, n)),
                    inputs: Inputs::sorted(vec![
                        Source::Dest(Dest::Reg(FakeReg::R2, Size::new(n, n))),
                        Source::Dest(Dest::Reg(FakeReg::R3, Size::qword())),
                    ]),
                    computation: None,
                    unobservable_external_inputs: false,
                })
                .collect::<Vec<_>>(),
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a,
            outputs: (0..16)
                .map(|n| Dataflow {
                    target: Dest::Reg(FakeReg::R1, Size::new(n, n)),
                    inputs: Inputs::sorted(vec![
                        Source::Dest(Dest::Reg(FakeReg::R2, Size::new(n, n))),
                        Source::Dest(Dest::Reg(FakeReg::R3, Size::qword())),
                    ]),
                    computation: None,
                    unobservable_external_inputs: false,
                })
                .collect::<Vec<_>>(),
            found_dependent_bytes: false,
        };
        assert_eq!(
            DataflowChange::compare_dataflows(&d1, &d2),
            vec![Some(DataflowChange {
                from: Location::Reg(FakeReg::R0),
                to: Location::Reg(FakeReg::R1),
                change_locations: vec![
                    ChangeLocation::Output(0),
                    ChangeLocation::Output(1),
                    ChangeLocation::Output(2),
                    ChangeLocation::Output(3),
                    ChangeLocation::Output(4),
                    ChangeLocation::Output(5),
                    ChangeLocation::Output(6),
                    ChangeLocation::Output(7),
                    ChangeLocation::Output(8),
                    ChangeLocation::Output(9),
                    ChangeLocation::Output(10),
                    ChangeLocation::Output(11),
                    ChangeLocation::Output(12),
                    ChangeLocation::Output(13),
                    ChangeLocation::Output(14),
                    ChangeLocation::Output(15)
                ]
            })]
        );
    }

    #[test]
    pub fn diff_byte_alignment() {
        let a = MemoryAccesses::<FakeArch> {
            instr: Instruction::new(&[]),
            memory: Vec::new(),
            use_trap_flag: false,
        };
        let d1 = Dataflows {
            addresses: a.clone(),
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R0, Size::new(0, 3)),
                inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::B0, Size::new(0, 3)))]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: a.clone(),
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::new(0, 0)),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::B0, Size::new(0, 3)))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::new(1, 1)),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::B0, Size::new(0, 3)))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::new(2, 2)),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::B0, Size::new(0, 3)))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::new(3, 3)),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::B0, Size::new(0, 3)))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        assert_eq!(DataflowChange::compare_dataflows(&d1, &d2), vec![None]);

        let d2 = Dataflows {
            addresses: a,
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::new(0, 0)),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::B0, Size::new(1, 1)))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::new(1, 1)),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::B0, Size::new(2, 2)))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::new(2, 2)),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::B0, Size::new(3, 3)))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R0, Size::new(3, 3)),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::B0, Size::new(3, 3)))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        assert_eq!(DataflowChange::compare_dataflows(&d1, &d2), vec![None]);
    }

    #[test]
    pub fn diff_dont_merge_flags() {
        let d1 = Dataflows {
            addresses: MemoryAccesses::<FakeArch> {
                instr: Instruction::new(&[]),
                memory: Vec::new(),
                use_trap_flag: false,
            },
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R0, Size::qword()),
                inputs: Inputs::sorted(vec![
                    Source::Dest(Dest::Reg(FakeReg::RF, Size::new(0, 0))),
                    Source::Dest(Dest::Reg(FakeReg::RF, Size::new(1, 1))),
                    Source::Dest(Dest::Reg(FakeReg::RF, Size::new(2, 2))),
                    Source::Dest(Dest::Reg(FakeReg::RF, Size::new(3, 3))),
                    Source::Dest(Dest::Reg(FakeReg::RF, Size::new(4, 4))),
                    Source::Dest(Dest::Reg(FakeReg::RF, Size::new(5, 5))),
                ]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: MemoryAccesses::<FakeArch> {
                instr: Instruction::new(&[]),
                memory: Vec::new(),
                use_trap_flag: false,
            },
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::R0, Size::new(1, 6)),
                inputs: Inputs::sorted(vec![
                    Source::Dest(Dest::Reg(FakeReg::RF, Size::new(0, 0))),
                    Source::Dest(Dest::Reg(FakeReg::RF, Size::new(1, 1))),
                    Source::Dest(Dest::Reg(FakeReg::RF, Size::new(2, 2))),
                    Source::Dest(Dest::Reg(FakeReg::RF, Size::new(3, 3))),
                    Source::Dest(Dest::Reg(FakeReg::RF, Size::new(4, 4))),
                    Source::Dest(Dest::Reg(FakeReg::RF, Size::new(5, 5))),
                ]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        assert_eq!(DataflowChange::compare_dataflows(&d1, &d2), vec![None]);
    }

    #[test]
    pub fn diff_dont_allow_entire_outputs_to_disappear() {
        let d1 = Dataflows {
            addresses: MemoryAccesses::<FakeArch> {
                instr: Instruction::new(&[]),
                memory: Vec::new(),
                use_trap_flag: false,
            },
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R1, Size::qword()),
                    inputs: Inputs::sorted(vec![
                        Source::Dest(Dest::Reg(FakeReg::R0, Size::qword())),
                        Source::Dest(Dest::Reg(FakeReg::R2, Size::qword())),
                        Source::Dest(Dest::Reg(FakeReg::R1, Size::qword())),
                    ]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::RF, Size::qword()),
                    inputs: Inputs::sorted(vec![
                        Source::Dest(Dest::Reg(FakeReg::R0, Size::qword())),
                        Source::Dest(Dest::Reg(FakeReg::R1, Size::qword())),
                    ]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: MemoryAccesses::<FakeArch> {
                instr: Instruction::new(&[]),
                memory: Vec::new(),
                use_trap_flag: false,
            },
            outputs: vec![Dataflow {
                target: Dest::Reg(FakeReg::RF, Size::qword()),
                inputs: Inputs::sorted(vec![
                    Source::Dest(Dest::Reg(FakeReg::R0, Size::qword())),
                    Source::Dest(Dest::Reg(FakeReg::R1, Size::qword())),
                ]),
                computation: None,
                unobservable_external_inputs: false,
            }],
            found_dependent_bytes: false,
        };
        assert_eq!(DataflowChange::compare_dataflows(&d1, &d2), vec![None]);
    }

    #[test]
    pub fn diff_correct_locations() {
        let d1 = Dataflows {
            addresses: MemoryAccesses::<FakeArch> {
                instr: Instruction::new(&[]),
                memory: Vec::new(),
                use_trap_flag: false,
            },
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R1, Size::new(0, 0)),
                    inputs: Inputs::sorted(vec![
                        Source::Dest(Dest::Reg(FakeReg::R0, Size::new(0, 0))),
                        Source::Dest(Dest::Reg(FakeReg::R1, Size::new(0, 0))),
                    ]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::R15, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R15, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::RF, Size::qword()),
                    inputs: Inputs::sorted(vec![
                        Source::Dest(Dest::Reg(FakeReg::R0, Size::new(0, 0))),
                        Source::Dest(Dest::Reg(FakeReg::R1, Size::new(0, 0))),
                    ]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        let d2 = Dataflows {
            addresses: MemoryAccesses::<FakeArch> {
                instr: Instruction::new(&[]),
                memory: Vec::new(),
                use_trap_flag: false,
            },
            outputs: vec![
                Dataflow {
                    target: Dest::Reg(FakeReg::R15, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R15, Size::qword()))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
                Dataflow {
                    target: Dest::Reg(FakeReg::RF, Size::qword()),
                    inputs: Inputs::sorted(vec![Source::Dest(Dest::Reg(FakeReg::R1, Size::new(0, 0)))]),
                    computation: None,
                    unobservable_external_inputs: false,
                },
            ],
            found_dependent_bytes: false,
        };
        assert_eq!(
            DataflowChange::compare_dataflows(&d1, &d2),
            vec![
                None,
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R0),
                    to: Location::Reg(FakeReg::R1),
                    change_locations: vec![ChangeLocation::InputForOutput {
                        output_index: 0,
                        input_index: 0
                    }]
                }),
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R0),
                    to: Location::Reg(FakeReg::R1),
                    change_locations: vec![
                        ChangeLocation::InputForOutput {
                            output_index: 0,
                            input_index: 0
                        },
                        ChangeLocation::InputForOutput {
                            output_index: 2,
                            input_index: 0
                        }
                    ]
                }),
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R0),
                    to: Location::Reg(FakeReg::R1),
                    change_locations: vec![ChangeLocation::InputForOutput {
                        output_index: 2,
                        input_index: 0
                    }]
                }),
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R0),
                    to: Location::Reg(FakeReg::RZ),
                    change_locations: vec![ChangeLocation::InputForOutput {
                        output_index: 2,
                        input_index: 0
                    }]
                }),
                Some(DataflowChange {
                    from: Location::Reg(FakeReg::R1),
                    to: Location::Reg(FakeReg::R0),
                    change_locations: vec![
                        ChangeLocation::Output(0),
                        ChangeLocation::InputForOutput {
                            output_index: 0,
                            input_index: 1
                        }
                    ]
                })
            ]
        );
    }
}
