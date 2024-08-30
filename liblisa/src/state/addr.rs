//! Abstractions over [memory addresses](Addr), [areas](Area) and [pages](Page).

use std::fmt::{Debug, Display, Formatter, LowerHex, Result, UpperHex};
use std::marker::PhantomData;
use std::ops::{Add, Sub};

use serde::{Deserialize, Serialize};

use crate::arch::Arch;

#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[repr(transparent)]
/// Represents a 64-bit memory address.
pub struct Addr(u64);

impl Addr {
    /// Creates a new address from an `u64`.
    #[inline]
    pub fn new(addr: u64) -> Addr {
        Addr(addr)
    }

    /// Converts the address into an area that starts at the current address and runs for `size` bytes.
    #[inline]
    pub fn into_area(self, size: u64) -> Area {
        Area::new(self, size)
    }

    /// Returns the page on which the address is located.
    #[inline]
    pub fn page<A: Arch>(self) -> Page<A> {
        Page(self.0 >> A::PAGE_BITS, PhantomData)
    }

    /// Aligns the address to the start of the page.
    #[inline]
    pub fn align_to_page_start(self, page_bits: usize) -> Addr {
        Addr((self.0 >> page_bits) << page_bits)
    }

    /// Counts the number of trailing zeros in the address.
    #[inline]
    pub fn trailing_zeros(self) -> u32 {
        self.0.trailing_zeros()
    }

    /// Converts the address to a `u64`.
    #[inline]
    pub fn as_u64(self) -> u64 {
        self.0
    }

    /// Computes the number of bytes between the address and `other`.
    #[inline]
    pub fn distance(self, other: Addr) -> u64 {
        if self.0 > other.0 {
            self.0 - other.0
        } else {
            other.0 - self.0
        }
    }

    /// Computes the number of bytes between the address and `other`.
    #[inline]
    pub fn distance_between(self, other: Addr) -> u64 {
        self.0.wrapping_sub(other.0).min(other.0.wrapping_sub(self.0))
    }
}

impl UpperHex for Addr {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        UpperHex::fmt(&self.0, f)
    }
}

impl LowerHex for Addr {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        UpperHex::fmt(&self.0, f)
    }
}

impl Debug for Addr {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        Debug::fmt(&self.0, f)
    }
}

impl Display for Addr {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        Display::fmt(&self.0, f)
    }
}

impl Add<u64> for Addr {
    type Output = Addr;

    #[inline]
    fn add(self, rhs: u64) -> Self::Output {
        Addr(self.0.wrapping_add(rhs))
    }
}

impl Sub<u64> for Addr {
    type Output = Addr;

    #[inline]
    fn sub(self, rhs: u64) -> Self::Output {
        Addr(self.0.wrapping_sub(rhs))
    }
}

impl Sub<Addr> for Addr {
    type Output = u64;

    #[inline]
    fn sub(self, rhs: Addr) -> Self::Output {
        self.0.wrapping_sub(rhs.0)
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// Represents a memory page.
///
/// Page size and alignment is determined according to [crate::arch::Arch::PAGE_BITS].
pub struct Page<A: Arch>(u64, PhantomData<*const A>);

impl<A: Arch> Copy for Page<A> {}

impl<A: Arch> Page<A> {
    /// Returns the lowest address on this page.
    #[inline]
    pub fn start_addr(&self) -> Addr {
        Addr(self.0 << A::PAGE_BITS)
    }

    /// Returns the last address of the page.
    /// This is always greater than the value returned by [`Self::start_addr`].
    #[inline]
    pub fn last_address_of_page(&self) -> Addr {
        Addr((self.0 << A::PAGE_BITS) | ((1 << A::PAGE_BITS) - 1))
    }

    /// Returns the first address after this page.
    /// This may wrap around if the page is the last page in the address space.
    /// In that case, the address returned is 0.
    #[inline]
    pub fn first_address_after_page(&self) -> Addr {
        Addr((self.0 + 1) << A::PAGE_BITS)
    }

    /// Converts [`Self::start_addr`] to a `u64`.
    #[inline]
    pub fn as_u64(self) -> u64 {
        self.0
    }
}

impl<A: Arch> Debug for Page<A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_struct("Page")
            .field("start", &self.start_addr())
            .field("end", &self.last_address_of_page())
            .field("index", &self.0)
            .finish()
    }
}

impl<A: Arch> Add<u64> for Page<A> {
    type Output = Page<A>;

    #[inline]
    fn add(self, rhs: u64) -> Self::Output {
        Page((self.0.wrapping_add(rhs) << A::PAGE_BITS) >> A::PAGE_BITS, PhantomData)
    }
}

impl<A: Arch> Sub<u64> for Page<A> {
    type Output = Page<A>;

    #[inline]
    fn sub(self, rhs: u64) -> Self::Output {
        Page((self.0.wrapping_sub(rhs) << A::PAGE_BITS) >> A::PAGE_BITS, PhantomData)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
/// Represents an arbitrary memory area between two [Addr]s.
///
/// Note that there are several edge-cases around wrapping.
/// For example, [`Area::first_address_after`] may return a number smaller than [`Area::start_addr`] if the area wraps around.
///
/// The functions implemented on `Area` take these edge-cases into account.
pub struct Area {
    addr: Addr,
    /// `size` should be smaller than 2**63.
    size: u64,
}

impl Area {
    #[inline]
    /// `size` should be smaller than 2**63.
    /// This is not checked.
    pub fn new(addr: Addr, size: u64) -> Area {
        Area {
            addr,
            size,
        }
    }

    #[inline]
    fn offset(self, offset: u64) -> Area {
        Area {
            addr: self.addr + offset,
            size: self.size,
        }
    }

    /// Returns true if the area contains the address `addr`.
    #[inline]
    pub fn contains(&self, addr: Addr) -> bool {
        if let Some(end_addr) = self.addr.0.checked_add(self.size) {
            self.size > 0 && addr >= self.addr && addr.0 < end_addr
        } else {
            // Shift both addresses by an offset.
            // Choosing this offset will align the area such that base = 0.
            // This will return a correct result for all possible values of `self.size`.
            let offset = self.size - self.addr.0.wrapping_add(self.size);
            self.offset(offset).contains(addr + offset)
        }
    }

    /// Returns the start address of the area
    #[inline]
    pub fn start_addr(&self) -> Addr {
        self.addr
    }

    /// Returns the end address of the area.
    /// May be smaller than the start address if the area wraps around.
    #[inline]
    fn end_addr(&self) -> u64 {
        self.addr.0.wrapping_add(self.size - 1)
    }

    /// Returns the first address after the area.
    /// May be smaller than the start address if the area wraps around.
    #[inline]
    pub fn first_address_after(&self) -> Addr {
        Addr(self.addr.0.wrapping_add(self.size))
    }

    /// Extends the start of the address by `size` bytes.
    #[inline]
    pub fn extend_before(&self, size: u64) -> Area {
        Area {
            addr: Addr(self.addr.0.wrapping_sub(size)),
            size: self.size + size,
        }
    }

    /// Returns true if the page of the first address in the area and the page of the last address in the area are different.
    #[inline]
    pub fn crosses_page_bounds(&self, page_bits: usize) -> bool {
        let start_index = self.start_addr().0 >> page_bits;
        let end_index = self.end_addr() >> page_bits;

        // Gives an incorrect result when size > 2**63, but this never happens.
        start_index != end_index
    }

    #[inline]
    fn expand_to_page<A: Arch>(&self) -> Area {
        let addr = self.addr.align_to_page_start(A::PAGE_BITS);

        // Correct the size for the alignment of addr.
        let new_size = self.size + (self.addr - addr);

        // Adjust the size such that the end also falls on a page bound.
        let size = ((new_size + ((1 << A::PAGE_BITS) - 1)) >> A::PAGE_BITS) << A::PAGE_BITS;

        Area {
            addr,
            size,
        }
    }

    /// Returns true if the areas have at least one page which is shared by both.
    #[inline]
    pub fn shares_page_with<A: Arch>(&self, other: &Area) -> bool {
        self.expand_to_page::<A>().overlaps_with(&other.expand_to_page::<A>())
    }

    #[inline]
    fn last_addr(&self) -> Option<Addr> {
        self.addr.0.checked_add(self.size - 1).map(Addr)
    }

    /// Returns true if the area overlaps with `other`.
    #[inline]
    pub fn overlaps_with(&self, other: &Area) -> bool {
        // println!("Checking overlap between {:?} and {:?}", self, other);
        match (self.last_addr(), other.last_addr()) {
            (Some(end), Some(other_end)) => other_end >= self.addr && other.addr <= end,
            (Some(_), None) | (None, Some(_)) => {
                let offset_self_to_0 = 0u64.wrapping_sub(self.addr.as_u64());
                let offset = if other.offset(offset_self_to_0).last_addr().is_some() {
                    offset_self_to_0
                } else {
                    0u64.wrapping_sub(other.addr.as_u64())
                };

                // println!("Offset = 0x{offset:X}");

                let new_self = self.offset(offset);
                let new_other = other.offset(offset);

                // println!("New self = {new_self:?}, new other = {new_other:?}");

                let end = new_self.last_addr().expect("Areas are too far apart");
                let other_end = new_other.last_addr().expect("Areas are too far apart");

                other_end >= new_self.addr && new_other.addr <= end
            },

            // If both areas wrap around, they both share at least the wrap around.
            (None, None) => true,
        }
    }

    /// Returns the size of the area.
    #[inline]
    pub fn size(&self) -> u64 {
        self.size
    }
}

impl Debug for Area {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "0x{:x}+0x{:x}", self.addr, self.size)
    }
}

#[cfg(test)]
mod tests {
    use crate::arch::fake::FakeArch;
    use crate::state::Addr;

    #[test]
    pub fn overlaps_with() {
        let a1 = Addr::new(0x1234).into_area(5);
        let a2 = Addr::new(0x1240).into_area(16);
        let a3 = Addr::new(0x1248).into_area(4);
        let a4 = Addr::new(0x1238).into_area(16);
        let a5 = Addr::new(0x1248).into_area(16);

        assert!(!a1.overlaps_with(&a2));

        assert!(a2.overlaps_with(&a3));
        assert!(a2.overlaps_with(&a4));
        assert!(a2.overlaps_with(&a5));

        let a6 = Addr::new(0xB3FFA).into_area(4);
        let a7 = Addr::new(0x1DE03361A000).into_area(8);
        assert!(!a6.overlaps_with(&a7));
        assert!(!a7.overlaps_with(&a6));
    }

    #[test]
    pub fn overlaps_with_overflow() {
        let last_16_bytes = Addr::new(0xffff_ffff_ffff_fff0).into_area(16);
        let wrap_16 = Addr::new(0xffff_ffff_ffff_fff0).into_area(32);
        let first_4_bytes = Addr::new(0).into_area(4);
        let first_20_bytes = Addr::new(0).into_area(20);

        assert!(last_16_bytes.overlaps_with(&wrap_16));
        assert!(wrap_16.overlaps_with(&first_4_bytes));
        assert!(first_20_bytes.overlaps_with(&wrap_16));
    }

    #[test]
    pub fn shares_page_with() {
        let last_16_bytes = Addr::new(0xffff_ffff_ffff_fff0).into_area(16);
        let wrap_16 = Addr::new(0xffff_ffff_ffff_fff0).into_area(32);
        let first_4_bytes = Addr::new(0).into_area(4);
        let first_20_bytes = Addr::new(0).into_area(20);

        assert!(!last_16_bytes.shares_page_with::<FakeArch>(&first_4_bytes));
        assert!(!last_16_bytes.shares_page_with::<FakeArch>(&first_20_bytes));
        assert!(last_16_bytes.shares_page_with::<FakeArch>(&wrap_16));
    }

    #[test]
    pub fn page_wrapping() {
        let addr1 = Addr::new(0xffff_ffff_ffff_fff0);
        let page1 = addr1.page::<FakeArch>();
        let addr2 = Addr::new(0);
        let page2 = addr2.page::<FakeArch>();

        assert_eq!(page1 + 1, page2);
        assert_eq!(page1, page2 - 1);
    }
}
