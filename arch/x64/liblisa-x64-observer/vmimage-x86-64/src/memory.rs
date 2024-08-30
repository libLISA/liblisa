use core::{fmt::Display, ops::Range, ptr};
use arr_macro::arr;
use arrayvec::ArrayVec;
use x86_64::{
    structures::paging::{FrameAllocator, OffsetPageTable, PageTable, PhysFrame, Size4KiB, PageSize, Mapper, Page, PageTableFlags, mapper::MapperFlush, PageTableIndex, page_table::PageTableEntry},
    PhysAddr, VirtAddr, registers::control::{Cr3, Cr3Flags},
};

use crate::serial_println;

/// Initialize a new OffsetPageTable.
///
/// This function is unsafe because the caller must guarantee that the
/// complete physical memory is mapped to virtual memory at the passed
/// `physical_memory_offset`. Also, this function must be only called once
/// to avoid aliasing `&mut` references (which is undefined behavior).
pub unsafe fn init(physical_memory_offset: VirtAddr) -> OffsetPageTable<'static> {
    let level_4_table = active_level_4_table(physical_memory_offset);
    OffsetPageTable::new(level_4_table, physical_memory_offset)
}

/// Returns a mutable reference to the active level 4 table.
///
/// This function is unsafe because the caller must guarantee that the
/// complete physical memory is mapped to virtual memory at the passed
/// `physical_memory_offset`. Also, this function must be only called once
/// to avoid aliasing `&mut` references (which is undefined behavior).
unsafe fn active_level_4_table(physical_memory_offset: VirtAddr) -> &'static mut PageTable {
    let (level_4_table_frame, _) = Cr3::read();

    let phys = level_4_table_frame.start_address();
    let virt = physical_memory_offset + phys.as_u64();
    let page_table_ptr: *mut PageTable = virt.as_mut_ptr();

    &mut *page_table_ptr // unsafe
}

/// simple frame allocator that functions like a bump allocator.
/// frames are never freed.
pub struct ContiguousFrameAllocator {
    base: PhysAddr,
    end: PhysAddr,
}

impl ContiguousFrameAllocator {
    pub fn new(base: PhysAddr, end: PhysAddr) -> ContiguousFrameAllocator {
        Self { base, end }
    }

    // if this method is called consecutively with the same page size `S`, the returned frames are guaranteed to be contiguous.
    pub fn allocate_frame<S: PageSize>(&mut self) -> PhysFrame<S> {
        // just skip a few frames so we have the address aligned
        // since the majority of allocations will be 4KiB, the wasted memory is acceptable
        let addr = self.base.align_up(S::SIZE);

        // unwrap: the address is always aligned because of the line above
        let result = PhysFrame::from_start_address(addr).unwrap();

        // update the base address so we don't allocate the same frames multiple times
        self.base = result.start_address() + result.size();

        if self.base >= self.end {
            panic!("Out of memory: please increase the available physical memory");
        }

        result
    }

    pub fn suballocator<S: PageSize>(&mut self, num_pages: usize) -> ContiguousFrameAllocator {
        let start = self.base.align_up(S::SIZE);
        let end = start + S::SIZE * num_pages as u64;

        self.base = end;
        if self.base >= self.end {
            panic!("Out of memory: please increase the available physical memory");
        }

        ContiguousFrameAllocator {
            base: start,
            end,
        }
    }
}

extern "C" {
    /// UNSAFE: this static functions as a pointer to the end of the ELF binary: do not attempt read its value
    pub static DATA_END: u8;
}

#[derive(Debug)]
pub struct MappedPage {
    pub virtual_address: VirtAddr,
    pub physical_address: PhysAddr,
}

impl MappedPage {
    // UNSAFETY: Must make sure nothing else is accessing the page at the same time
    pub unsafe fn write(&mut self, offset: usize, buf: &[u8]) {
        // Make sure the write doesn't run off the page
        debug_assert!(offset + buf.len() <= 4096);

        ptr::copy_nonoverlapping(buf.as_ptr(), (self.virtual_address.as_u64() + offset as u64) as *mut u8, buf.len());
    }

    // UNSAFETY: Must make sure nothing else is accessing the page at the same time
    pub unsafe fn read(&self, offset: usize, buf: &mut [u8]) {
        // Make sure the read doesn't run off the page
        debug_assert!(offset + buf.len() <= 4096);

        ptr::copy_nonoverlapping((self.virtual_address.as_u64() + offset as u64) as *const u8, buf.as_mut_ptr(), buf.len());
    }
}

const MAX_PAGE_TABLES: usize = 800;

pub struct PageMapper {
    first_mapped_page: VirtAddr,
    next_page: VirtAddr,
    alloc: ContiguousFrameAllocator,
    pub phys_to_virt_offset: u64,
    pts_used: ContiguousFrameAllocator,// Bitmap<MAX_PAGE_TABLES>,
    first_page_table: PhysAddr,
}

impl PageMapper {
    /// UNSAFETY: 
    ///     - You may not call this function more than once.
    ///     - You must ensure physical memory is correctly mapped at the offset `physical_memory_offset` before calling this function.
    ///     - This function modifies CR3; anything that's not mapped in the executable region will be deleted.
    ///     - `keep_start` must point to the start of the memory region that must remain mapped in the new page table.
    ///         If you have not modified the linker script, this will be the start address (low address) of the kernel stack.
    pub unsafe fn init(physical_memory_offset: VirtAddr, mut alloc: ContiguousFrameAllocator, keep_start: u64) -> PageMapper {
        let start_addr = VirtAddr::new((&DATA_END as *const _) as u64).align_up(Size4KiB::SIZE);
        serial_println!("Keeping data between 0x{:x}-0x{:x}", keep_start, start_addr);
        serial_println!("Allocating extra data starting at 0x{:x}", start_addr);

        let page_frames = alloc.suballocator::<Size4KiB>(MAX_PAGE_TABLES);
        let first_frame: PhysFrame<Size4KiB> = PhysFrame::from_start_address(page_frames.base).unwrap();

        // first create a pagemapper that works with the old page tabes
        // we need this so we can write to the new page tables
        let next_page = start_addr + Size4KiB::SIZE * MAX_PAGE_TABLES as u64;
        let phys_to_virt_offset = physical_memory_offset.as_u64();
        let mut mapper = PageMapper {
            first_mapped_page: VirtAddr::new(keep_start),
            next_page,
            alloc,
            phys_to_virt_offset,
            pts_used: page_frames,
            first_page_table: first_frame.start_address(),
        };

        // create an empty level 4 page table
        let (pt_addr, pt) = mapper.allocate_page_table();
        assert_eq!(pt_addr, first_frame.start_address(), "The page table must be allocated in first_frame (0x{:x})", first_frame.start_address());
        *pt = PageTable::new();

        // Initialize all level 3 page tables as empty
        for i in 0..512 {
            let (p3_addr, p3) = mapper.allocate_page_table();
            assert_eq!(p3_addr, first_frame.start_address() + 4096u64 * (i + 1));

            (*pt)[i as usize].set_frame(PhysFrame::from_start_address(p3_addr).unwrap(), PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::USER_ACCESSIBLE);
            *p3 = PageTable::new();
        }

        // copy the currently mapped .text/.data sections from which we're running
        serial_println!("Copying kernel to new address...");
        let mut new_pt = OffsetPageTable::new(&mut *pt, physical_memory_offset);
        mapper.clone_pages(active_level_4_table(physical_memory_offset), &mut new_pt, physical_memory_offset.as_u64(), 4, 0, &(keep_start..start_addr.as_u64()));

        // map the extra pages
        // we can ignore the flush here because the new pagetable is not yet active
        // once we switch page tables we do a full TLB flush
        serial_println!("Mapping extra page table pages");
        for i in 0..MAX_PAGE_TABLES {
            let phys_addr = first_frame.start_address() + Size4KiB::SIZE * i as u64;
            let virt_addr = start_addr + Size4KiB::SIZE * i as u64;
            let flags = PageTableFlags::PRESENT | PageTableFlags::NO_EXECUTE | PageTableFlags::WRITABLE;

            serial_println!("Mapping {} (phys_addr={:X}, virt_addr={:X})", i, phys_addr, virt_addr);

            // ! NOTE: unsafe
            Mapper::<Size4KiB>::map_to_with_table_flags(&mut new_pt,
                Page::containing_address(virt_addr),
                PhysFrame::from_start_address(phys_addr).unwrap(),
                flags,
                PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::USER_ACCESSIBLE,
                &mut mapper
            ).unwrap().ignore();
        }

        // switch to the new page table
        // ! NOTE: unsafe
        Cr3::write(first_frame, Cr3Flags::empty());

        // now that we have updated CR3 we can start using the new virtual addresses
        serial_println!("Physical address 0x{:x} corresponds to virtual address 0x{:x}", first_frame.start_address(), start_addr);
        mapper.phys_to_virt_offset = start_addr.as_u64() - first_frame.start_address().as_u64();
        serial_println!("Computed offset to be 0x{:x}", mapper.phys_to_virt_offset);
        serial_println!("All data is now allocated between 0x{:x}-0x{:x}", keep_start, mapper.next_page);
        mapper
    }

    /// UNSAFETY: must ensure that no more than one instance of OffsetPageTable exists at any time
    unsafe fn get_p4(&self) -> OffsetPageTable<'static> {
        let p4 = (self.first_page_table.as_u64() + self.phys_to_virt_offset) as *mut _;
        OffsetPageTable::new(&mut *p4, VirtAddr::new(self.phys_to_virt_offset))
    }

    pub fn allocate_new_page(&mut self) -> MappedPage {
        let frame = self.alloc.allocate_frame::<Size4KiB>();
        let phys_addr = frame.start_address();
        let virt_addr = self.next_page;
        self.next_page += frame.size();

        serial_println!("New frame: phys=0x{:x}, mapped to virt=0x{:x}", phys_addr, virt_addr);
        unsafe {
            let mut pt = self.get_p4();
            let flags = PageTableFlags::PRESENT | PageTableFlags::NO_EXECUTE | PageTableFlags::WRITABLE | PageTableFlags::GLOBAL;
            Mapper::<Size4KiB>::map_to_with_table_flags(&mut pt,
                Page::containing_address(virt_addr),
                PhysFrame::from_start_address(phys_addr).unwrap(),
                flags,
                PageTableFlags::WRITABLE | PageTableFlags::USER_ACCESSIBLE | PageTableFlags::PRESENT,
                self
            ).unwrap().flush();
        }

        MappedPage {
            virtual_address: virt_addr,
            physical_address: frame.start_address(),
        }
    }

    pub fn map_physical_range(&mut self, start: PhysAddr, size: usize) -> VirtAddr {
        serial_println!("Mapping physical range 0x{:x}-0x{:x} to virtual addresses 0x{:x}-0x{:x}", start, start + size, self.next_page, self.next_page + size);

        let num_pages = size as u64 / Size4KiB::SIZE;
        let mapped_start_addr = self.next_page;
        for page_index in 0..num_pages {
            let phys_addr = start + page_index * Size4KiB::SIZE;
            unsafe {
                let mut pt = self.get_p4();
                let flags = PageTableFlags::PRESENT | PageTableFlags::NO_EXECUTE | PageTableFlags::WRITABLE | PageTableFlags::GLOBAL;
                Mapper::<Size4KiB>::map_to_with_table_flags(&mut pt,
                    Page::containing_address(self.next_page),
                    PhysFrame::from_start_address(phys_addr).unwrap(),
                    flags,
                    PageTableFlags::WRITABLE | PageTableFlags::USER_ACCESSIBLE | PageTableFlags::PRESENT,
                    self
                ).unwrap().flush();
            }

            self.next_page += Size4KiB::SIZE;
        }

        mapped_start_addr
    }

    pub fn freeze(mut self) -> UserPageMapper {
        let pt = (self.first_page_table.as_u64() + self.phys_to_virt_offset) as *mut PageTable;
        let frames = arr! [ self.allocate_frame().unwrap(); 48 ];

        // Clear the allocated page tables
        for frame in frames.iter() {
            let pt = (frame.start_address().as_u64() + self.phys_to_virt_offset) as *mut PageTable;
            unsafe {
                (*pt).zero();
            }
        }

        UserPageMapper {
            reserved: self.first_mapped_page..self.next_page,
            l3_page_tables: pt.wrapping_add(1),
            frame_allocator: BumpFrameAllocator::new(self.phys_to_virt_offset, frames),
            entries_to_clear: ArrayVec::new(),
        }
    }

    fn allocate_page_table(&mut self) -> (PhysAddr, *mut PageTable) {
        let phys_addr = self.allocate_frame().unwrap();
        let virt_addr = VirtAddr::new(phys_addr.start_address().as_u64() + self.phys_to_virt_offset);

        (phys_addr.start_address(), virt_addr.as_mut_ptr())
    }

    fn clone_pages(&mut self, from: &PageTable, to: &mut OffsetPageTable, phys_offset: u64, level: u8, addr: u64, range: &Range<u64>) {
        for (index, entry) in from.iter().enumerate().filter(|(_, e)| !e.is_unused()) {
            let addr = addr | ((index as u64) << (3 + level * 9));
            let end_addr = addr | ((index as u64 + 1) << (3 + level * 9));
            if level > 1 {
                serial_println!("Entering level {} at address {:X?} (ptr = {:X?})", level, addr, entry.addr().as_u64() + phys_offset);

                if end_addr < range.start || addr > range.end {
                    serial_println!("Skipping, not in range");
                } else {
                    self.clone_pages(unsafe { &*((entry.addr().as_u64() + phys_offset) as *const PageTable) }, to, phys_offset, level - 1, addr, range);
                }
            } else if range.contains(&addr) {
                serial_println!("Copying mapping for 0x{addr:x}", addr = addr);

                // we can ignore the flush here because the new pagetable is not yet active
                // once we switch page tables we do a full TLB flush
                unsafe {
                    Mapper::<Size4KiB>::map_to_with_table_flags(to, 
                        Page::containing_address(VirtAddr::new(addr)), 
                        PhysFrame::from_start_address(entry.addr()).unwrap(),
                        entry.flags() | PageTableFlags::GLOBAL,
                        PageTableFlags::WRITABLE | PageTableFlags::USER_ACCESSIBLE | PageTableFlags::PRESENT,
                        self
                    )
                }.unwrap().flush();
            }
        }
    }
}

unsafe impl FrameAllocator<Size4KiB> for PageMapper {
    fn allocate_frame(&mut self) -> Option<PhysFrame> {
        Some(self.pts_used.allocate_frame::<Size4KiB>())
    }
}

pub struct BumpFrameAllocator {
    /// The page frames that we'll use to map user pages.
    /// Worst case, each of the 16 mapped pages will be on a different L1, L2 & L3 page.
    /// Therefore we need at most 48 page tables to always be able to map all of them.
    page_frames: [PhysFrame; 48],
    next_unused_page_frame_index: usize,
    pub phys_to_virt_offset: u64,
}

impl BumpFrameAllocator {
    pub fn new(phys_to_virt_offset: u64, page_frames: [PhysFrame; 48]) -> BumpFrameAllocator {
        BumpFrameAllocator {
            page_frames,
            next_unused_page_frame_index: 0,
            phys_to_virt_offset,
        }
    }

    fn alloc_frame(&mut self) -> (PhysFrame, VirtAddr) {
        let frame = self.page_frames[self.next_unused_page_frame_index];
        self.next_unused_page_frame_index += 1;

        (frame, VirtAddr::new(frame.start_address().as_u64() + self.phys_to_virt_offset))
    }

    pub fn reset(&mut self) {
        self.next_unused_page_frame_index = 0;
    }
}

/// The user page mapper can map up to 16 pages into userspace.
/// It is not possible to individually unmap pages.
/// All mapped pages can be reset in one go with [`UserPageMapper::reset`].
/// After resetting, 16 new pages can be mapped into userspace.
/// 
/// You can think of this page mapper as a sort of bump allocator.
/// It can allocate the resources for mapping at most 16 pages.
pub struct UserPageMapper {
    reserved: Range<VirtAddr>,
    l3_page_tables: *mut PageTable,
    frame_allocator: BumpFrameAllocator,
    entries_to_clear: ArrayVec<*mut PageTableEntry, 64>,
}

impl UserPageMapper {
    #[inline]
    pub fn reserved_range(&self) -> Range<VirtAddr> {
        self.reserved.clone()
    }

    fn add_or_create_pt<'a>(&mut self, pt: &'a mut PageTable, index: PageTableIndex) -> &'a mut PageTable {
        let entry = &mut pt[index];
        let flags = PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::USER_ACCESSIBLE;
        if entry.is_unused() {
            let (phys_frame, virt_addr) = self.frame_allocator.alloc_frame();
            entry.set_frame(phys_frame, flags);

            unsafe {
                self.entries_to_clear.push(entry);
                &mut *(virt_addr.as_mut_ptr() as *mut PageTable)
            }
        } else {
            // The L{2,3} tables also need the USER_ACCESSIBLE/WRITABLE flags set.
            // We make sure of this in PageMapper, which always maps with parent table flags USER_ACCESSIBLE and WRITABLE.
            unsafe {
                &mut *((pt[index].addr().as_u64() + self.frame_allocator.phys_to_virt_offset) as *mut PageTable)
            }
        }
    }

    #[inline]
    pub fn map_user_direct(&mut self, frame: PhysFrame, page: Page, flags: PageTableFlags) {
        if self.reserved.contains(&page.start_address()) {
            panic!("Cannot map onto a reserved address: {:X?} is in reserved range {:X?}", page.start_address(), self.reserved);
        }

        let p4_index = (page.start_address().as_u64() >> 12 >> 9 >> 9 >> 9) & 0b1_1111_1111;
        let p3 = unsafe { &mut *self.l3_page_tables.wrapping_add(p4_index as usize) };
        let p2 = self.add_or_create_pt(p3, page.p3_index());
        let p1 = self.add_or_create_pt(p2, page.p2_index());

        let flags = flags | PageTableFlags::PRESENT | PageTableFlags::USER_ACCESSIBLE;
        let entry = &mut p1[page.p1_index()];
        entry.set_frame(frame, flags);

        self.entries_to_clear.push(entry);

        // We *must* flush here, even if we didn't access the page yet and it's unlikely we will
        MapperFlush::new(page).flush();
    }

    #[inline]
    pub fn reset_before(&mut self) {
        while let Some(entry) = self.entries_to_clear.pop() {
            unsafe { 
                (*entry).set_unused();
            }
        }

        self.frame_allocator.reset();
    }

    #[inline]
    pub fn unmap_hint(&mut self, page: Page) {
        // TODO: We might be able to skip this flush if the next observation maps the same page, we should delay flushing here and only do it once we have mapped the new pages and know if we still need to flush or if we already did in map_user_direct.
        MapperFlush::new(page).flush();
    }

    #[inline]
    pub fn reset_after(&mut self) { }
}

struct Padding(usize);

impl Display for Padding {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        for _ in 0..self.0 * 4 {
            f.write_str(" ")?;
        }

        Ok(())
    }
}

pub fn print_page_table(ptd: &PageTable, phys_offset: VirtAddr, addr: u64, level: u8) {
    let pad = Padding((4 - level) as usize);
    serial_println!("{}Level {}", pad, level);
    for i in 0..(1 << 9) {
        let entry = &ptd[i];
        if !entry.is_unused() {
            let addr = addr | ((i as u64) << (3 + level * 9));
            serial_println!("{pad}{i:3X} [{i:9b}]: 0x{full_addr:x} -> 0x{phys_addr:x} [flags: {flags:b}]", pad = pad, i = i, phys_addr = entry.addr(), full_addr = addr, flags = entry.flags());

            if level > 1 {
                print_page_table(unsafe { &*((entry.addr().as_u64() + phys_offset.as_u64()) as *const PageTable) }, phys_offset, addr, level - 1);
            }
        }
    }
}