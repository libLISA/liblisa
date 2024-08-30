//! Defines [`InstructionCounter`], which can be used to iterate and tunnel over instruction space.

use std::fmt::Debug;

use serde::{Deserialize, Serialize};

use crate::instr::set::FilterList;
use crate::instr::tree::FilterTree;
use crate::instr::Instruction;

/// A counter for iteration over instruction space.
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Clone, Serialize, Deserialize)]
pub struct InstructionCounter {
    data: [u8; 32],
    len: usize,
    end: Option<Instruction>,
    tunnel_pos: usize,
    num_tunneled: usize,
}

impl Debug for InstructionCounter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("InstructionCounter")
            .field("$current", &format!("{:X}", self.current()))
            .field("data", &self.data)
            .field("len", &self.len)
            .field("end", &self.end)
            .field("tunnel_pos", &self.tunnel_pos)
            .field("num_tunneled", &self.num_tunneled)
            .finish()
    }
}

impl InstructionCounter {
    /// Sets the current instruction to `instr`.
    pub fn set_current(&mut self, instr: &Instruction) {
        self.data[0..instr.byte_len()].copy_from_slice(instr.bytes());
        self.len = instr.byte_len();
        self.tunnel_pos = instr.byte_len() - 1;
    }

    /// Creates an instruction counter with the current position set to `start` and the end at `end` if it is not `None`.
    pub fn range(start: &Instruction, end: Option<Instruction>) -> InstructionCounter {
        let mut result = InstructionCounter {
            data: [0u8; 32],
            len: start.byte_len(),
            end,
            tunnel_pos: start.byte_len() - 1,
            num_tunneled: 0,
        };
        result.data[0..start.byte_len()].copy_from_slice(start.bytes());

        result
    }

    fn extend_internal(&mut self, fast_tunnel: bool) {
        self.data[self.len] = 0;
        self.len += 1;

        if !fast_tunnel {
            self.tunnel_pos = self.len - 1;
            self.num_tunneled = 0;
        }
    }

    /// Increases the length of the current instruction by one byte.
    /// If this causes any instruction filter to match, the current instruction may advance.
    pub fn extend(&mut self, filters: &FilterList, fast_tunnel: bool) -> bool {
        self.extend_internal(fast_tunnel);
        self.apply_filters_to_current(filters, false)
    }

    /// Reduces the length of the current instruction by one byte.
    /// If this causes any instruction filter to match, the current instruction may advance.
    pub fn reduce(&mut self, filters: &FilterList, fast_tunnel: bool) -> bool {
        self.len -= 1;
        self.data[self.len] = 0;
        if !fast_tunnel || self.tunnel_pos >= self.len {
            self.tunnel_pos = self.len - 1;
            self.num_tunneled = 0;
        }

        self.apply_filters_to_current(filters, true)
    }

    fn next_single(&mut self) -> bool {
        loop {
            let i = self.tunnel_pos;
            if let Some(v) = self.data[i].checked_add(1) {
                self.data[i] = v;
                break;
            } else if self.tunnel_pos == 0 {
                self.data.fill(0xff);
                return false;
            } else {
                self.data[i] = 0;
                self.tunnel_pos -= 1;
            }
        }

        if let Some(end) = self.end {
            self.current() <= end
        } else {
            true
        }
    }

    /// Applys the filters to the current instruction.
    /// The current instruction is advanced to the first (lexicographically) instruction after the current instruction, which does not match any of the filters.
    pub fn apply_filters_to_current(&mut self, filters: &FilterList, mut was_reduced_last: bool) -> bool {
        if self.data.iter().all(|&x| x == 0xff) {
            return false;
        }

        // let mut seen = VecDeque::new();
        let mut tree = None; // FilterTree::new();

        loop {
            // We shouldn't start extending again if we just reduced the length
            if !was_reduced_last {
                // If all bytes in the instruction match, but the filter is longer, we can extend by a single byte.
                while filters.should_extend(&self.current()) {
                    self.extend_internal(false);
                }
            }

            was_reduced_last = false;

            // Inlined self.current() to make the borrow checker happy
            // This allows the compiler to understand that we're only taking a reference &self.data, and not &self entirely
            if let Some(matching_filter) = filters.matching_filter(&self.current()) {
                let tree = match &mut tree {
                    Some(tree) => tree,
                    None => {
                        tree = Some(FilterTree::new());
                        let tree = tree.as_mut().unwrap();

                        if let Some(ref end) = self.end {
                            tree.filter_above(end);
                        }

                        tree
                    },
                };
                if tree.len() >= 0x100_0000 {
                    println!("Tree too big ({}), pruning.", tree.len());

                    while tree.len() >= 0x100_0000 {
                        tree.prune(&self.current());
                    }

                    println!("New tree length: {}", tree.len());

                    if let Some(ref end) = self.end {
                        tree.filter_above(end);
                    }
                }

                tree.filter(matching_filter);

                println!(
                    "Filtering: {:?} (in {:?} -- tree_size={})",
                    matching_filter,
                    self.current(),
                    tree.len()
                );
                if let Some(next) = tree.find_next(&self.current()) {
                    // println!("Found next: {:?}", next);
                    tree.filter_below(&self.current());
                    self.set_current(&next);
                } else {
                    return false;
                }
            } else {
                if let Some(end) = self.end {
                    if self.current() > end {
                        return false;
                    }
                }

                return true;
            }
        }
    }

    /// Tunnels to the next instruction.
    /// If this causes any instruction filter to match, the current instruction may advance.
    pub fn tunnel_next(&mut self, filters: &FilterList, tunnel_delay: usize) -> bool {
        self.num_tunneled += 1;
        if self.num_tunneled < tunnel_delay || self.tunnel_pos >= self.len {
            self.tunnel_pos = self.len - 1;
        }

        if !self.next_single() {
            return false;
        }

        if self.num_tunneled < tunnel_delay {
            self.len = self.tunnel_pos + 1;
        }
        self.apply_filters_to_current(filters, false)
    }

    /// Tunnels to the next instruction, without looking at instruction filters.
    pub fn tunnel_next_ignore_filters(&mut self) -> bool {
        if !self.next_single() {
            return false;
        }

        true
    }

    /// The current position of the counter.
    pub fn current(&self) -> Instruction {
        Instruction::new(&self.data[0..self.len])
    }

    /// Returns the next 256 instructions, assuming we're tunneling via the "happy path".
    /// The happy path occurs when the instruction length does not change at all.
    ///
    /// Returns None if the byte at the tunnel position is not 00.
    pub fn next_happy_group(&self) -> Option<Vec<Instruction>> {
        if self.data[self.tunnel_pos] < 220 {
            Some(
                (self.data[self.tunnel_pos]..=0xff)
                    .map(|b| {
                        let mut data = self.data;
                        data[self.tunnel_pos] = b;

                        Instruction::new(&data[0..self.len])
                    })
                    .collect(),
            )
        } else {
            None
        }
    }

    /// The tunneling position.
    /// This is the byte index in the instruction that will be incremented next.
    pub fn tunnel_pos(&self) -> usize {
        self.tunnel_pos
    }

    /// Replaces the tunneling position with the new `tunnel_pos`.
    pub fn set_tunnel_pos(&mut self, tunnel_pos: usize) {
        assert!(tunnel_pos < self.len);
        self.tunnel_pos = tunnel_pos;
        self.data[tunnel_pos + 1..].fill(0);
    }

    /// Replaces the end of the counter with `end`, or removes the end if `end` is `None`.
    pub fn set_end(&mut self, end: Option<Instruction>) {
        self.end = end;
    }

    /// Returns the end of the counter.
    pub fn end(&self) -> Option<Instruction> {
        self.end
    }
}

#[cfg(test)]
mod tests {
    use crate::instr::counter::InstructionCounter;
    use crate::instr::set::FilterList;
    use crate::instr::{ByteFilter, Instruction, InstructionFilter};

    #[test]
    pub fn count_next() {
        let mut c = InstructionCounter::range(&Instruction::new(&[0x00]), None);
        assert_eq!(c.current(), [0x00].as_ref().into());

        c.tunnel_next(&FilterList::new(), 200);
        assert_eq!(c.current(), [0x01].as_ref().into());

        c.tunnel_next(&FilterList::new(), 200);
        assert_eq!(c.current(), [0x02].as_ref().into());
    }

    #[test]
    pub fn count_range() {
        let mut c = InstructionCounter::range(&Instruction::new(&[0x14]), Some(Instruction::new(&[0x18])));

        assert_eq!(c.current(), [0x14].as_ref().into());

        assert!(c.tunnel_next(&FilterList::new(), 200));
        assert_eq!(c.current(), [0x15].as_ref().into());

        assert!(c.tunnel_next(&FilterList::new(), 200));
        assert_eq!(c.current(), [0x16].as_ref().into());

        assert!(c.tunnel_next(&FilterList::new(), 200));
        assert_eq!(c.current(), [0x17].as_ref().into());

        assert!(c.tunnel_next(&FilterList::new(), 200));
        assert_eq!(c.current(), [0x18].as_ref().into());

        assert!(!c.tunnel_next(&FilterList::new(), 200));
    }

    #[test]
    pub fn count_extend() {
        let mut c = InstructionCounter::range(&Instruction::new(&[0x00]), None);
        assert_eq!(c.current(), [0x00].as_ref().into());

        c.extend(&FilterList::new(), false);
        assert_eq!(c.current(), [0x00, 0x00].as_ref().into());

        c.tunnel_next(&FilterList::new(), 200);
        assert_eq!(c.current(), [0x00, 0x01].as_ref().into());
    }

    #[test]
    pub fn count_overflow() {
        let mut c = InstructionCounter::range(&Instruction::new(&[0x00]), None);
        assert_eq!(c.current(), [0x00].as_ref().into());

        c.extend(&FilterList::new(), false);
        assert_eq!(c.current(), [0x00, 0x00].as_ref().into());

        c.extend(&FilterList::new(), false);
        assert_eq!(c.current(), [0x00, 0x00, 0x00].as_ref().into());

        let mut f = FilterList::new();
        for n in 0..=0xff {
            f.add(InstructionFilter::new(vec![
                ByteFilter::new(0xff, 0x00),
                ByteFilter::new(0xff, 0x00),
                ByteFilter::new(0xff, n),
            ]));

            c.apply_filters_to_current(&f, false);
        }

        assert_eq!(c.current(), [0x00, 0x01].as_ref().into());

        c.extend(&f, false);
        assert_eq!(c.current(), [0x00, 0x01, 0x00].as_ref().into());
    }

    #[test]
    pub fn count_finish() {
        let mut c = InstructionCounter::range(&Instruction::new(&[0x00]), None);
        assert_eq!(c.current(), [0x00].as_ref().into());

        for _ in 0..255 {
            assert!(c.tunnel_next(&FilterList::new(), 200));
        }

        assert!(!c.tunnel_next(&FilterList::new(), 200));
    }

    #[test]
    pub fn counter_end_complex() {
        let mut c = InstructionCounter::range(&Instruction::new(&[0x45, 0x40]), Some(Instruction::new(&[0x47, 0x19, 0x1B])));
        assert_eq!(c.current(), [0x45, 0x40].as_ref().into());
        let mut f = FilterList::new();
        for _ in 0..0xC0 {
            assert!(c.tunnel_next(&f, 200));
        }

        assert_eq!(c.current(), [0x46].as_ref().into());
        c.extend(&f, false);

        for n in 0..=0xff {
            f.add(InstructionFilter::new(vec![
                ByteFilter::new(0xff, 0x46),
                ByteFilter::new(0xff, n),
            ]));
            assert!(c.apply_filters_to_current(&f, false));
        }

        // Because the end is set at <47191B>, we can assume that <47> is too short for an instruction.
        assert_eq!(c.current(), [0x47, 0x00].as_ref().into());

        for _ in 0..0x19 {
            assert!(c.tunnel_next(&f, 200));
        }

        println!("Current: {:X}", c.current());
        assert_eq!(c.current(), [0x47, 0x19].as_ref().into());
        c.extend(&f, false);

        for n in 0..0x1B {
            println!("Remaining {}: {:X}", n, c.current());
            assert!(c.tunnel_next(&f, 200));
        }

        assert!(!c.tunnel_next(&f, 200));
    }

    #[test]
    pub fn test_filter1() {
        let mut c = InstructionCounter::range(&Instruction::new(&[0x00]), None);
        assert_eq!(c.current(), [0x00].as_ref().into());

        let mut f = FilterList::new();

        f.add(InstructionFilter::new(vec![ByteFilter::new(0b0000_0001, 0b00000000)]));

        for i in 0..128 {
            assert!(c.tunnel_next(&f, 200));
            assert_eq!(c.current(), [1 + i * 2].as_ref().into());
        }

        assert!(!c.tunnel_next(&f, 200));
    }

    #[test]
    pub fn test_filter2() {
        let mut c = InstructionCounter::range(&Instruction::new(&[0x00]), None);
        assert_eq!(c.current(), [0x00].as_ref().into());
        let mut f = FilterList::new();

        let filter = InstructionFilter::new(vec![ByteFilter::new(0b1111_0010, 0b00000010)]);
        println!("Filter: {filter:?}");
        f.add(filter);

        for i in [0b0001, 0b0100, 0b0101, 0b1000, 0b1001, 0b1100, 0b1101]
            .iter()
            .cloned()
            .chain(16..=255)
        {
            assert!(c.tunnel_next(&f, 200));
            assert_eq!(c.current(), [i].as_ref().into());
        }

        assert!(!c.tunnel_next(&f, 200));
    }

    #[test]
    pub fn test_apply_filter() {
        let mut c = InstructionCounter::range(&Instruction::new(&[0x00]), None);
        assert_eq!(c.current(), [0x00].as_ref().into());
        let mut f = FilterList::new();

        f.add(InstructionFilter::new(vec![ByteFilter::new(0b1111_1100, 0b0000_0000)]));

        assert!(c.apply_filters_to_current(&f, false));
        assert_eq!(c.current(), [0x04].as_ref().into());
    }

    #[test]
    pub fn test_filter_partial() {
        let mut c = InstructionCounter::range(&Instruction::new(&[0x00]), None);
        let mut f = FilterList::new();
        c.extend(&f, false);
        assert_eq!(c.current(), [0x00, 0x00].as_ref().into());

        f.add(InstructionFilter::new(vec![
            ByteFilter::new(0, 0),
            ByteFilter::new(0b1000_0000, 0b0000_0000),
        ]));

        for i in 128..=255 {
            assert!(c.tunnel_next(&f, 200));
            assert_eq!(c.current(), [0x00, i].as_ref().into());
        }

        assert!(c.tunnel_next(&f, 200));
        // assert_eq!(c.current(), [ 0x01 ].as_ref().into());

        // c.extend(&f, false);
        assert_eq!(c.current(), [0x01, 0b1000_0000].as_ref().into());
    }

    #[test_log::test]
    pub fn test_filter_nesting() {
        let mut c = InstructionCounter::range(&Instruction::new(&[0x00]), None);
        let mut f = FilterList::new();
        c.extend(&f, false);
        c.extend(&f, false);
        c.extend(&f, false);
        assert_eq!(c.current(), [0x00, 0x00, 0x00, 0x00].as_ref().into());

        for i in 0..8 {
            f.add(InstructionFilter::new(vec![
                ByteFilter::new(0b0010_0001, 0),
                ByteFilter::new(0b1111_1111, 0),
                ByteFilter::new(0b1111_1111, 0),
                ByteFilter::new(1 << i, 1 << i),
            ]));
        }

        assert!(c.tunnel_next(&f, 200));
        assert_eq!(c.current(), [0x00, 0x00, 0x01].as_ref().into());

        assert!(c.extend(&f, false));
        assert_eq!(c.current(), [0x00, 0x00, 0x01, 0x00].as_ref().into());

        for i in 0..8 {
            f.add(InstructionFilter::new(vec![
                ByteFilter::new(0b0010_0001, 0),
                ByteFilter::new(0b1111_1111, 0),
                ByteFilter::new(1 << i, 1 << i),
                ByteFilter::new(0, 0),
            ]));
        }

        assert!(c.tunnel_next(&f, 200));
        assert_eq!(c.current(), [0x00, 0x01].as_ref().into());

        assert!(c.extend(&f, false));
        assert_eq!(c.current(), [0x00, 0x01, 0x00].as_ref().into());

        assert!(c.extend(&f, false));
        assert_eq!(c.current(), [0x00, 0x01, 0x00, 0x00].as_ref().into());

        assert!(c.tunnel_next(&f, 200));
        assert_eq!(c.current(), [0x00, 0x01, 0x00, 0x01].as_ref().into());
    }

    #[test_log::test]
    pub fn instr_ord() {
        assert!(Instruction::new(&[0x0F]) < Instruction::new(&[0x0F, 0xFF]));
        assert!(Instruction::new(&[0x0F, 0xFF]) > Instruction::new(&[0x0F]));
        assert!(Instruction::new(&[0x0F, 0xFF]) >= Instruction::new(&[0x0F]));
    }

    #[test_log::test]
    pub fn counter_end() {
        let mut c = InstructionCounter::range(&Instruction::new(&[0x0E]), Some(Instruction::new(&[0x0F, 0xFF])));
        assert_eq!(c.current(), [0x0E].as_ref().into());

        assert!(c.tunnel_next(&FilterList::new(), 200));
        assert_eq!(c.current(), [0x0F].as_ref().into());
    }

    #[test_log::test]
    pub fn test_filter_merge() {
        let mut c = InstructionCounter::range(&Instruction::new(&[0x02, 0x15, 0x82, 0x09, 0x00, 0x00]), None);
        let mut f = FilterList::new();
        assert_eq!(c.current(), [0x02, 0x15, 0x82, 0x09, 0x00, 0x00].as_ref().into());

        for i in 0..8 {
            f.add(InstructionFilter::new(vec![
                ByteFilter::new(0b1101_0110, 0b0000_0010),
                ByteFilter::new(0b0100_0111, 0b0000_0101),
                ByteFilter::new(0, 0),
                ByteFilter::new(0, 0),
                ByteFilter::new(0, 0),
                ByteFilter::new(1 << i, 1 << i),
            ]));
        }

        for i in 0..8 {
            f.add(InstructionFilter::new(vec![
                ByteFilter::new(0b1101_0110, 0b0000_0010),
                ByteFilter::new(0b0100_0111, 0b0000_0101),
                ByteFilter::new(0, 0),
                ByteFilter::new(0, 0),
                ByteFilter::new(1 << i, 1 << i),
                ByteFilter::new(0, 0),
            ]));
        }

        for i in 4..8 {
            f.add(InstructionFilter::new(vec![
                ByteFilter::new(0b1101_0110, 0b0000_0010),
                ByteFilter::new(0b0100_0111, 0b0000_0101),
                ByteFilter::new(0, 0),
                ByteFilter::new(1 << i, 1 << i),
                ByteFilter::new(0, 0),
                ByteFilter::new(0, 0),
            ]));
        }

        for i in 0..4 {
            f.add(InstructionFilter::new(vec![
                ByteFilter::new(0b1101_0110, 0b0000_0010),
                ByteFilter::new(0b0100_0111, 0b0000_0101),
                ByteFilter::new(0, 0),
                ByteFilter::new(1 << i, 1 << i),
                ByteFilter::new(0xff, 0),
                ByteFilter::new(0xff, 0),
            ]));
        }

        println!("{c:?}");

        assert!(c.apply_filters_to_current(&f, false));
        assert_eq!(c.current(), [0x02, 0x15, 0x83, 0x00, 0x00, 0x00].as_ref().into());
    }

    #[test_log::test]
    pub fn test_filter_merge_complex() {
        let f1 = InstructionFilter::parse("01000100 11110110 01010100 __111111 ________");
        let f2 = InstructionFilter::parse("00001111 00010111 01___100 ___0__1_ ________");

        assert!(f1.try_merge(&f2).is_none());

        let f1 = InstructionFilter::parse("01000100 11110110 01010100 __111111 ________");
        let f2 = InstructionFilter::parse("____111_ ____0111 01___100 ___0__1_ ________");

        assert!(f1.try_merge(&f2).is_none());

        let f1 = InstructionFilter::parse("01000__0 1111___0 01010100 __111111 ________");
        let f2 = InstructionFilter::parse("____111_ ____0111 01___100 ___0__1_ ________");

        assert!(f1.try_merge(&f2).is_none());
    }

    #[test]
    pub fn test_filter_match_instr() {
        let f = InstructionFilter::parse("00001111 00010111 01___100 __111111 ________");
        assert!(f.matches(&Instruction::new(&[0x0F, 0x17, 0x74, 0xFF, 0x00])));
    }

    #[test]
    pub fn test_filter_performance() {
        let mut c = InstructionCounter::range(&Instruction::new(&[0x00]), None);
        let mut f = FilterList::new();
        c.extend(&f, false);
        c.extend(&f, false);
        c.extend(&f, false);
        c.extend(&f, false);
        c.extend(&f, false);

        assert_eq!(c.current(), [0x00, 0x00, 0x00, 0x00, 0x00, 0x00].as_ref().into());

        f.add(InstructionFilter::new(vec![
            ByteFilter::new(0b1111_1111, 0b0000_0000),
            ByteFilter::new(0b0000_0000, 0),
            ByteFilter::new(0b0000_0000, 0),
            ByteFilter::new(0b0000_0000, 0),
            ByteFilter::new(0b0000_0000, 0),
            ByteFilter::new(0b0000_0000, 0),
        ]));

        for i in 1..=255 {
            assert!(c.tunnel_next(&f, 200));
            assert_eq!(c.current(), [i].as_ref().into());
        }

        assert!(!c.tunnel_next(&f, 200));
    }

    #[test]
    pub fn test_simple_next_step() {
        let mut c = InstructionCounter::range(&[0x45, 0xFF, 0xA4, 0x00, 0x00, 0x00, 0x00, 0x00].as_ref().into(), None);
        let mut f = FilterList::new();

        assert_eq!(c.current(), [0x45, 0xFF, 0xA4, 0x00, 0x00, 0x00, 0x00, 0x00].as_ref().into());

        assert!(c.tunnel_next(&f, 200));

        f.add(InstructionFilter::new(vec![
            ByteFilter::new(0b1111_0011, 0x41),
            ByteFilter::new(0xff, 0xff),
            ByteFilter::new(0xff, 0xA4),
            ByteFilter::new(0, 0),
            ByteFilter::new(0, 0),
            ByteFilter::new(0, 0),
            ByteFilter::new(0, 0),
        ]));

        assert!(c.apply_filters_to_current(&f, false));

        assert_eq!(c.current(), [0x45, 0xFF, 0xA5].as_ref().into());
    }

    #[test]
    pub fn test_next_step2() {
        let mut c = InstructionCounter::range(&[0x0F, 0x17, 0x74, 0x29, 0x00].as_ref().into(), None);
        let mut f = FilterList::new();

        assert_eq!(c.current(), [0x0F, 0x17, 0x74, 0x29, 0x00].as_ref().into());

        f.add(InstructionFilter::parse("00001111 00010111 01110000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01110001 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01110010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01110011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01110101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01110110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01110111 ________"));
        f.add(InstructionFilter::parse(
            "00001111 1010_100 10___000 ________ ________ ________ ________ ___00000",
        ));
        f.add(InstructionFilter::parse(
            "00001111 1010_100 10___001 ________ ________ ________ ________ ___00000",
        ));
        f.add(InstructionFilter::parse(
            "00001111 1010_100 10___010 ________ ________ ________ ________ ___00000",
        ));
        f.add(InstructionFilter::parse(
            "00001111 1010_100 10___011 ________ ________ ________ ________ ___00000",
        ));
        f.add(InstructionFilter::parse(
            "00001111 1010_100 10___101 ________ ________ ________ ________ ___00000",
        ));
        f.add(InstructionFilter::parse(
            "00001111 1010_100 10___110 ________ ________ ________ ________ ___00000",
        ));
        f.add(InstructionFilter::parse(
            "00001111 1010_100 10___111 ________ ________ ________ ________ ___00000",
        ));
        f.add(InstructionFilter::parse("00001111 00010111 01010100 ___00000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 ___0__1_ ________"));
        f.add(InstructionFilter::parse("01001_00 00110011 01___100 ___00000 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __000000 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __000001 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __000010 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __000011 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __000100 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __000101 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __000110 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __000111 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __000001 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __000010 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __000011 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __000100 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __000101 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __000110 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __000111 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __010000 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __010001 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __010010 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __010011 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __010100 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __010101 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __010110 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __010111 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __010001 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __010010 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __010011 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __010100 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __010101 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __010110 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __010111 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __011000 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __011001 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __011010 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __011011 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __011100 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __011101 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __011110 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __011111 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __011001 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __011010 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __011011 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __011100 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __011101 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __011110 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __011111 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __100000 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __100001 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __100010 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __100011 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __100100 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __100101 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __100110 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __100111 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __100001 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __100010 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __100011 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __100100 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __100101 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __100110 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __100111 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __101000 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __101001 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __101010 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __101011 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __101100 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __101101 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __101110 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __101111 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __101001 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __101010 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __101011 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __101100 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __101101 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __101110 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __101111 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __110000 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __110001 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __110010 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __110011 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __110100 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __110101 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __110110 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __110111 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __110001 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __110010 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __110011 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __110100 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __110101 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __110110 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __110111 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __111000 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __111001 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __111010 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __111011 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __111100 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __111101 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __111110 ________"));
        f.add(InstructionFilter::parse("01000100 11110110 01010100 __111111 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __111001 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __111010 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __111011 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __111100 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __111101 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __111110 ________"));
        f.add(InstructionFilter::parse("01000101 11110110 01010100 __111111 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __000000 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __000001 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __000010 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __000011 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __000100 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __000101 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __000110 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __000111 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __000001 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __000010 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __000011 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __000100 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __000101 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __000110 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __000111 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __001000 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __001001 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __001010 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __001011 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __001100 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __001101 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __001110 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __001111 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __001001 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __001010 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __001011 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __001100 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __001101 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __001110 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __001111 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __010000 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __010001 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __010010 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __010011 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __010100 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __010101 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __010110 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __010111 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __010001 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __010010 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __010011 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __010100 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __010101 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __010110 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __010111 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __011000 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __011001 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __011010 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __011011 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __011100 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __011101 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __011110 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __011111 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __011001 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __011010 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __011011 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __011100 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __011101 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __011110 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __011111 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __100000 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __100001 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __100010 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __100011 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __100100 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __100101 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __100110 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __100111 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __100001 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __100010 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __100011 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __100100 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __100101 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __100110 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __100111 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __101000 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __101001 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __101010 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __101011 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __101100 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __101101 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __101110 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __101111 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __101001 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __101010 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __101011 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __101100 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __101101 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __101110 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __101111 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __110000 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __110001 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __110010 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __110011 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __110100 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __110101 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __110110 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __110111 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __110001 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __110010 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __110011 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __110100 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __110101 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __110110 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __110111 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __111000 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __111001 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __111010 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __111011 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __111100 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __111101 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __111110 ________"));
        f.add(InstructionFilter::parse("01000110 11110110 01010100 __111111 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __111001 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __111010 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __111011 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __111100 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __111101 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __111110 ________"));
        f.add(InstructionFilter::parse("01000111 11110110 01010100 __111111 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __000000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __000010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __000011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __000100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __000101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __000110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __000111 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __001000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __001010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __001011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __001100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __001101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __001110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __001111 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011111 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100111 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101111 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110111 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111111 ________"));

        println!("Before: {:X}", c.current());
        assert!(c.apply_filters_to_current(&f, false));

        println!("Advanced one: {:X}", c.current());

        f.add(InstructionFilter::parse("00001111 00010111 01___100 __001000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __001001 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __001010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __001011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __001100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __001101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __001110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __010000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __010001 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __010010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __010011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __010100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __010101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __010110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011001 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100001 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101001 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110001 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111001 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111110 ________"));

        println!("Before applying filters = {:X}", c.current());
        assert!(c.apply_filters_to_current(&f, false));
        println!("Current = {:X}", c.current());

        assert_eq!(c.current(), [0x0F, 0x17, 0x74, 0x41].as_ref().into());
    }

    #[test]
    pub fn test_next_step3() {
        let mut c = InstructionCounter::range(&[0x0F, 0x17, 0x74, 0x12, 0x00].as_ref().into(), None);
        let mut f = FilterList::new();

        f.add(InstructionFilter::parse("00001111 00010111 01110000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01110001 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01110010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01110011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01110101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01110110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01110111 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 ___00000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01010100 ___00000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 ____0__1 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __000000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __000001 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __000011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __000100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __000101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __000110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __000111 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __010000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __010001 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __010011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __010100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __010101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __010110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __010111 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011001 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011111 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100001 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100111 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101001 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101111 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110001 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110111 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111001 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111111 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 ___0__1_ ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __000000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __000010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __000011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __000100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __000101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __000110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __000111 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __001000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __001010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __001011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __001100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __001101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __001110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __001111 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __011111 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __100111 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __101111 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __110111 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111000 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111011 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111100 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111101 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111110 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __111111 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __001001 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __001001 ________"));

        assert!(c.apply_filters_to_current(&f, false));

        f.add(InstructionFilter::parse("00001111 00010111 01___100 __010010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01___100 __010010 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 011110__ ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01_____1 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01_____1 ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01____1_ ________"));
        f.add(InstructionFilter::parse("00001111 00010111 01____1_ ________"));
        f.add(InstructionFilter::parse(
            "00001111 00010111 100000__ ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 ___00000 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 ___00000 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 ____0__1 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __000000 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __000001 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __000011 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __000100 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __000101 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __000110 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __000111 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __010000 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __010001 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __010011 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __010100 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __010101 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __010110 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __010111 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __011000 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __011001 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __011011 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __011100 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __011101 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __011110 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __011111 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __100000 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __100001 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __100011 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __100100 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __100101 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __100110 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __100111 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __101000 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __101001 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __101011 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __101100 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __101101 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __101110 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __101111 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __110000 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __110001 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __110011 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __110100 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __110101 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __110110 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __110111 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __111000 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __111001 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __111011 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __111100 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __111101 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __111110 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00001111 00010111 10___100 __111111 ________ ________ ________ ________",
        ));

        assert!(c.apply_filters_to_current(&f, false));

        println!("Current = {:X}", c.current());

        assert_eq!(c.current(), [0x0F, 0x17, 0x84, 0x02].as_ref().into());
    }

    #[test]
    pub fn test_counter_merge() {
        let mut c = InstructionCounter::range(
            &Instruction::new(&[0x0F, 0xAC, 0x9C, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
            None,
        );
        let mut f = FilterList::new();

        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ _____010",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ _____0_1",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ _____100",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ ______01",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ ______10",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ _______1",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 1010_100 10___100 ___00000 ________ ________ ________ ________ ___0000_",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ ___0001_",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ ___0010_",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ ___00_1_",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ ___0100_",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ ___0_010",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ ___0_0_1",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ ___0_100",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ ___0__01",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ ___0__10",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ ___0___1",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ ___1000_",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ ____0010",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ ____00_1",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ ____0100",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ ____0_01",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ ____0_10",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ ____0__1",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ ____1000",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "00001111 10101100 10___100 ___00000 ________ ________ ________ ________ _____001",
        ));

        assert!(c.apply_filters_to_current(&f, false));

        assert_eq!(c.current(), Instruction::new(&[0x0F, 0xAC, 0x9C, 0x01]));
    }

    #[test]
    pub fn test_counter_next_step4() {
        let mut c = InstructionCounter::range(&Instruction::new(&[0x03, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]), None);
        let mut f = FilterList::new();

        f.add(InstructionFilter::parse(
            "00000011 10___100 00000000 ________ ________ ________ ________",
        ));
        f.add(InstructionFilter::parse(
            "00000011 10___100 ___00000 ________ ________ ________ ________",
        ));
        assert!(c.apply_filters_to_current(&f, false));

        println!("Currently: {:X}", c.current());

        assert_eq!(c.current(), Instruction::new(&[0x03, 0x84, 0x01]));
    }

    #[test]
    pub fn test_next_step5() {
        let mut c = InstructionCounter::range(&[0x43, 0xC0, 0x04, 0x05, 0x00, 0x17, 0xCB, 0x9C].as_ref().into(), None);
        let mut f = FilterList::new();

        assert_eq!(c.current(), [0x43, 0xC0, 0x04, 0x05, 0x00, 0x17, 0xCB, 0x9C].as_ref().into());

        f.add(InstructionFilter::parse(
            "01000___ 11000000 00___100 _____101 ________ ________ ________ ________ ___00000",
        ));
        f.add(InstructionFilter::parse(
            "0100____ 11000000 00000100 _____101 ________ ________ ________ ________ _______1",
        ));
        f.add(InstructionFilter::parse(
            "0100____ 11000000 00000100 _____101 ________ ________ ________ ________ ______1_",
        ));
        f.add(InstructionFilter::parse(
            "0100____ 11000000 00000100 _____101 ________ ________ ________ ________ _____1__",
        ));
        f.add(InstructionFilter::parse(
            "0100____ 11000000 00000100 _____101 ________ ________ ________ ________ ____1___",
        ));
        f.add(InstructionFilter::parse(
            "0100____ 11000000 00000100 _____101 ________ ________ ________ ________ ___1____",
        ));
        assert!(c.apply_filters_to_current(&f, false));

        println!("Currently: {:X}", c.current());

        assert_eq!(c.current(), Instruction::new(&[0x43, 0xC0, 0x04, 0x06]));
    }

    #[test]
    pub fn test_next_step6() {
        let mut c = InstructionCounter::range(&[0xC0, 0x24, 0x05, 0x00, 0x02, 0x70, 0x1A, 0x00].as_ref().into(), None);
        let mut f = FilterList::new();

        f.add(InstructionFilter::parse(
            "11000000 0010_100 _____101 ________ ________ ________ ________ ____0000",
        ));
        f.add(InstructionFilter::parse(
            "11000000 001_0100 _____101 ________ ________ ________ ________ ___00___",
        ));
        f.add(InstructionFilter::parse(
            "11000000 001_0100 _____101 ________ ________ ________ ________ ___0_000",
        ));
        f.add(InstructionFilter::parse(
            "11000000 0010_100 _____101 ________ ________ ________ ________ ____1__1",
        ));
        f.add(InstructionFilter::parse(
            "11000000 0010_100 _____101 ________ ________ ________ ________ ____1_1_",
        ));
        f.add(InstructionFilter::parse(
            "11000000 0010_100 _____101 ________ ________ ________ ________ ____11__",
        ));
        f.add(InstructionFilter::parse(
            "11000000 0010_100 _____101 ________ ________ ________ ________ ___1____",
        ));
        assert!(c.apply_filters_to_current(&f, false));

        println!("Currently: {:X}", c.current());

        assert_eq!(c.current(), Instruction::new(&[0xC0, 0x24, 0x06]));
    }

    #[test]
    pub fn test_next_step7() {
        let mut c = InstructionCounter::range(&[0xC0, 0x2C, 0x05, 0x00, 0x05, 0xC3, 0xE4].as_ref().into(), None);
        let mut f = FilterList::new();

        c.extend(&f, false);

        f.add(InstructionFilter::parse(
            "11000000 0010_100 _____101 ________ ________ ________ ________ ______00",
        ));
        f.add(InstructionFilter::parse(
            "11000000 0010_100 _____101 ________ ________ ________ ________ _____00_",
        ));
        f.add(InstructionFilter::parse(
            "11000000 0010_100 _____101 ________ ________ ________ ________ _____0_0",
        ));
        f.add(InstructionFilter::parse(
            "11000000 0010_100 _____101 ________ ________ ________ ________ ____0___",
        ));
        f.add(InstructionFilter::parse(
            "11000000 0010_100 _____101 ________ ________ ________ ________ ______00",
        ));
        f.add(InstructionFilter::parse(
            "11000000 0010_100 _____101 ________ ________ ________ ________ _____00_",
        ));
        f.add(InstructionFilter::parse(
            "11000000 0010_100 _____101 ________ ________ ________ ________ _____0_0",
        ));
        f.add(InstructionFilter::parse(
            "11000000 0010_100 _____101 ________ ________ ________ ________ ______11",
        ));
        f.add(InstructionFilter::parse(
            "11000000 0010_100 _____101 ________ ________ ________ ________ ______00",
        ));
        f.add(InstructionFilter::parse(
            "11000000 0010_100 _____101 ________ ________ ________ ________ _____1_1",
        ));
        f.add(InstructionFilter::parse(
            "11000000 001__100 _____101 ________ ________ ________ ________ _____11_",
        ));
        assert!(c.apply_filters_to_current(&f, false));

        println!("Currently: {:X}", c.current());

        assert_eq!(c.current(), Instruction::new(&[0xC0, 0x2C, 0x06]));
    }

    #[test]
    pub fn test_next_step8() {
        let mut c = InstructionCounter::range(&[0xC0, 0xB5, 0x00, 0xA1, 0x65, 0xEF].as_ref().into(), None);
        let mut f = FilterList::new();

        c.extend(&f, false);

        f.add_nomerge(InstructionFilter::parse(
            "11000000 101_0__1 ________ ________ ________ ________ ____0___",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "11000000 101_0__1 ________ ________ ________ ________ ___1____",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "11000000 101_0__1 ________ ________ ________ ________ ____11__",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "11000000 101_0__1 ________ ________ ________ ________ ____1_1_",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "11000000 101_0__1 ________ ________ ________ ________ ____1__1",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "11000000 101_0__1 ________ ________ ________ ________ _____000",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "11000000 1011___1 ________ ________ ________ ________ ___00___",
        ));
        assert!(c.apply_filters_to_current(&f, false));

        println!("Currently: {:X}", c.current());

        assert_eq!(c.current(), Instruction::new(&[0xC0, 0xB6]));
    }

    #[test]
    pub fn test_next_step9() {
        let mut c = InstructionCounter::range(&[0xC0, 0xB5].as_ref().into(), None);
        let mut f = FilterList::new();

        f.add_nomerge(InstructionFilter::parse(
            "11000000 101_0__1 ________ ________ ________ ________ ____0___",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "11000000 101_0__1 ________ ________ ________ ________ ___1____",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "11000000 101_0__1 ________ ________ ________ ________ ____11__",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "11000000 101_0__1 ________ ________ ________ ________ ____1_1_",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "11000000 101_0__1 ________ ________ ________ ________ ____1__1",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "11000000 101_0__1 ________ ________ ________ ________ _____000",
        ));
        f.add_nomerge(InstructionFilter::parse(
            "11000000 1011___1 ________ ________ ________ ________ ___00___",
        ));
        assert!(c.apply_filters_to_current(&f, false));

        println!("Currently: {:X}", c.current());

        assert_eq!(c.current(), Instruction::new(&[0xC0, 0xB6]));
    }

    #[test]
    pub fn test_simple_next_step_partial_mask() {
        let mut c = InstructionCounter::range(&[0x45, 0xFF, 0xA4, 0x00, 0x00, 0x00, 0x00, 0x00].as_ref().into(), None);
        let mut f = FilterList::new();

        assert_eq!(c.current(), [0x45, 0xFF, 0xA4, 0x00, 0x00, 0x00, 0x00, 0x00].as_ref().into());

        assert!(c.apply_filters_to_current(&f, false));

        f.add(InstructionFilter::new(vec![
            ByteFilter::new(0b1111_0011, 0x41),
            ByteFilter::new(0xff, 0xff),
            ByteFilter::new(0b10110110, 0xA4),
            ByteFilter::new(0, 0),
            ByteFilter::new(0, 0),
            ByteFilter::new(0, 0),
            ByteFilter::new(0, 0),
        ]));

        assert!(c.apply_filters_to_current(&f, false));

        assert_eq!(c.current(), [0x45, 0xFF, 0xA6].as_ref().into());
    }

    #[test]
    pub fn test_filter_wildcard_count() {
        assert_eq!(
            InstructionFilter::new(vec![
                ByteFilter::new(0b1111_1001, 0b0000_0000),
                ByteFilter::new(0b0000_0000, 0),
                ByteFilter::new(0b0011_0000, 0),
            ])
            .num_wildcard_bits(),
            16
        );
    }

    #[test]
    pub fn normal_tunneling() {
        let mut c = InstructionCounter::range(&Instruction::new(&[0x00]), None);
        let f = FilterList::new();
        c.extend(&f, false);
        c.extend(&f, false);

        assert_eq!(c.current(), [0, 0, 0].as_ref().into());
        for b in 1..=255u8 {
            assert!(c.tunnel_next(&f, 200));
            assert_eq!(c.current(), [0, 0, b].as_ref().into());
        }

        for b in 1..=255u8 {
            assert!(c.tunnel_next(&f, 200));
            assert_eq!(c.current(), [0, b, 0].as_ref().into());
        }

        assert!(c.tunnel_next(&f, 200));
        assert_eq!(c.current(), [1, 0, 0].as_ref().into());
        c.reduce(&f, false);
        assert_eq!(c.current(), [1, 0].as_ref().into());

        for b in 1..=255u8 {
            assert!(c.tunnel_next(&f, 200));
            assert_eq!(c.current(), [1, b].as_ref().into());
        }

        assert!(c.tunnel_next(&f, 200));
        assert_eq!(c.current(), [2, 0].as_ref().into());

        assert!(c.tunnel_next(&f, 200));
        assert_eq!(c.current(), [3, 0].as_ref().into());

        assert!(c.extend(&f, false));
        assert_eq!(c.current(), [3, 0, 0].as_ref().into());
        for b in 1..=255u8 {
            assert!(c.tunnel_next(&f, 200));
            assert_eq!(c.current(), [3, 0, b].as_ref().into());
        }
    }

    #[test]
    pub fn fast_tunneling() {
        let mut c = InstructionCounter::range(&Instruction::new(&[0x00]), None);
        let f = FilterList::new();
        c.extend(&f, false);
        c.extend(&f, false);

        assert_eq!(c.current(), [0, 0, 0].as_ref().into());
        for b in 1..=255u8 {
            assert!(c.tunnel_next(&f, 200));
            assert_eq!(c.current(), [0, 0, b].as_ref().into());
        }

        for b in 1..=255u8 {
            assert!(c.tunnel_next(&f, 200));
            assert_eq!(c.current(), [0, b, 0].as_ref().into());
        }

        assert!(c.tunnel_next(&f, 200));
        assert_eq!(c.current(), [1, 0, 0].as_ref().into());
        c.reduce(&f, true);
        assert_eq!(c.current(), [1, 0].as_ref().into());

        for b in 2..=255u8 {
            assert!(c.tunnel_next(&f, 200));
            assert_eq!(c.current(), [b, 0].as_ref().into());
        }

        assert!(!c.tunnel_next(&f, 200));
    }

    #[test]
    pub fn test_tunneling2() {
        let mut c = InstructionCounter::range(&Instruction::new(&[0x4f, 0x8e, 0x87, 0x01, 0x1d, 0xc5, 0x00]), None);
        let f = FilterList::new();
        for _ in 0..255 {
            assert!(c.tunnel_next(&f, 200));
        }

        assert_eq!(c.current(), [0x4f, 0x8e, 0x87, 0x01, 0x1d, 0xc5, 0xff].as_ref().into());

        assert!(c.tunnel_next(&f, 200));
        assert!(c.apply_filters_to_current(&f, false));
        assert_eq!(c.current(), [0x4f, 0x8e, 0x87, 0x01, 0x1d, 0xc6, 0x00].as_ref().into());

        assert!(c.tunnel_next(&f, 200));
        assert!(c.apply_filters_to_current(&f, false));
        assert_eq!(c.current(), [0x4f, 0x8e, 0x87, 0x01, 0x1d, 0xc7, 0x00].as_ref().into());

        assert!(c.tunnel_next(&f, 200));
        assert!(c.apply_filters_to_current(&f, false));
        assert_eq!(c.current(), [0x4f, 0x8e, 0x87, 0x01, 0x1d, 0xc8, 0x00].as_ref().into());

        assert!(c.tunnel_next(&f, 200));
        assert!(c.apply_filters_to_current(&f, false));
        assert_eq!(c.current(), [0x4f, 0x8e, 0x87, 0x01, 0x1d, 0xc9, 0x00].as_ref().into());
    }

    #[test]
    pub fn test_tunnel_delay() {
        let mut c = InstructionCounter::range(&Instruction::new(&[0x44, 0xff]), None);
        let f = FilterList::new();
        assert!(c.tunnel_next(&f, 200));

        assert_eq!(c.current(), [0x45].as_ref().into());

        assert!(c.extend(&f, true));

        assert_eq!(c.current(), [0x45, 0x00].as_ref().into());

        assert!(c.tunnel_next(&f, 200));
        assert_eq!(c.current(), [0x45, 0x01].as_ref().into());
    }

    #[test]
    pub fn test_tunnel_no_skipping() {
        let mut c = InstructionCounter::range(&Instruction::new(&[0x45, 0xff, 0x9d]), None);
        let mut f = FilterList::new();

        f.add(InstructionFilter::new(vec![
            ByteFilter::new(0xF0, 0x40),
            ByteFilter::new(0b01111110, 0b01111110),
            ByteFilter::new(0b00000010, 0b00000010),
        ]));

        f.add(InstructionFilter::new(vec![
            ByteFilter::new(0xF0, 0x40),
            ByteFilter::new(0b10110111, 0b10110111),
            ByteFilter::new(0b00001100, 0),
            ByteFilter::new(0, 0),
            ByteFilter::new(0, 0),
            ByteFilter::new(0, 0),
            ByteFilter::new(0, 0),
        ]));

        f.add(InstructionFilter::new(vec![
            ByteFilter::new(0xF0, 0x40),
            ByteFilter::new(0b01111110, 0b01111110),
            ByteFilter::new(0b00100000, 0b00100000),
        ]));

        f.add(InstructionFilter::new(vec![
            ByteFilter::new(0xF0, 0x40),
            ByteFilter::new(0b01111110, 0b01111110),
            ByteFilter::new(0b01000000, 0b01000000),
        ]));

        assert!(c.tunnel_next(&f, 200));
        println!("Current: {:X}", c.current());
        assert_eq!(c.current(), [0x46, 0x00].as_ref().into());
    }

    #[test]
    pub fn test_no_extend_after_reduce() {
        let mut c = InstructionCounter::range(&Instruction::new(&[0x0E, 0x00]), None);
        let mut f = FilterList::new();

        f.add(InstructionFilter::parse("00001__0 11100000"));

        assert!(c.reduce(&f, false));
        println!("Current: {:X}", c.current());
        assert_eq!(c.current(), [0x0E].as_ref().into());
    }
}
