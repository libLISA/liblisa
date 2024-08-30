use super::caselist::CaseIndex;

#[derive(Clone, Debug)]
struct Entry<S> {
    match_true: Vec<CaseIndex>,
    match_false: Vec<CaseIndex>,
    synthesizer: S,
    last_use_tick: u64,
}

/// The SynthesizerCache can store used synthesizers.
/// These synthesizers already have some cases applied on them.
/// It saves some time when multiple iterations or multiple groups use identical or almost identical synthesizers.
#[derive(Clone, Debug)]
pub struct SynthesizerCache<S> {
    synthesizers: Vec<Entry<S>>,
    tick: u64,
}

impl<S> Default for SynthesizerCache<S> {
    fn default() -> Self {
        Self {
            synthesizers: Vec::new(),
            tick: 0,
        }
    }
}

impl<S> SynthesizerCache<S> {
    pub fn tick(&mut self) {
        self.tick += 1;

        self.synthesizers.retain(|item| item.last_use_tick + 2 > self.tick);
    }

    /// Returns the closest synthesizer that we can find as a tuple of `(synthesizer, is_exact)`.
    /// `is_exact` indicates whether the synthesizer has exactly matched all cases.
    pub fn get(&mut self, match_true: &[CaseIndex], match_false: &[CaseIndex]) -> Option<(&S, bool)> {
        self.synthesizers
            .iter_mut()
            .filter(|entry| {
                entry.match_true.iter().all(|c| match_true.contains(c))
                    && entry.match_false.iter().all(|c| match_false.contains(c))
            })
            .max_by_key(|entry| entry.match_true.len() + entry.match_false.len())
            .map(|s| {
                s.last_use_tick = self.tick;
                (
                    &s.synthesizer,
                    s.match_true.len() == match_true.len() && s.match_false.len() == match_false.len(),
                )
            })
    }

    pub fn add(&mut self, match_true: &[CaseIndex], match_false: &[CaseIndex], synthesizer: S) {
        self.synthesizers.push(Entry {
            match_true: match_true.to_vec(),
            match_false: match_false.to_vec(),
            synthesizer,
            last_use_tick: self.tick,
        })
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.synthesizers.len()
    }
}
