use core::arch::asm;

use liblisa_x64_observer_shmqueue::frame::command::{Permissions, CommandFrame};
use x86_64::{VirtAddr, structures::paging::Page};
use crate::userspace::jmp_to_usermode;

pub struct Observer {}

pub trait ObservationMapper {
    /// Maps a new page into userspace.
    fn map(&mut self, frame_index: usize, page: Page, permissions: Permissions);

    /// Maps a new page into userspace.
    fn map_executable(&mut self, frame_index: usize, page: Page, addr: u64, permissions: Permissions);

    /// Hints to the mapper that we're about to use the changes we made in map() or reset().
    fn ready_hint(&mut self);

    /// Resets all mappings. 
    /// [`ObservationMapper::unmap_hint`] must correctly hint all mapped pages after this function is called.
    fn reset_before(&mut self);

    /// Hints to the mapper that the specified page can now be unmapped.
    /// A call to [`ObservationMapper::reset`] must follow before [`ObservationMapper::map`] can be called again.
    fn unmap_hint(&mut self, page: Page);

    /// Resets all mappings. 
    /// [`ObservationMapper::unmap_hint`] must correctly hint all mapped pages before this function is called.
    fn reset_after(&mut self);
}

fn valid_address(addr: u64) -> bool {
    addr >= 0xffff_8000_0000_0000 || addr <= 0x0000_7fff_ffff_ffff
}

impl Observer {
    pub fn new() -> Observer {
        Observer { }
    }

    pub fn observe<'a>(&mut self, mapper: &mut impl ObservationMapper, allowed_component_bitmap: u64, cmd: &mut CommandFrame) {
        if !valid_address(cmd.gpregs.fs_base) || !valid_address(cmd.gpregs.gs_base) {
            cmd.gpregs.exception_id = 13;
            return;
        }

        for request in cmd.memory_mappings.active().iter() {
            // SAFETY: page_start_addr is guaranteed to return an address with the lower 12 bits all 0.
            let requested_page = unsafe { Page::from_start_address_unchecked(VirtAddr::new(request.page_start_addr())) };
            if request.permissions() == Permissions::Executable {
                mapper.map_executable(request.frame_index() as usize, requested_page, cmd.gpregs.rip, request.permissions());
            } else {
                mapper.map(request.frame_index() as usize, requested_page, request.permissions());
            }
        }

        mapper.ready_hint();

        unsafe {
            let component_bitmap = cmd.restore_extended_registers;
            cmd.extended_regs.restore(component_bitmap & allowed_component_bitmap).unwrap();
        }

        let debug_regs = &mut cmd.debug_regs;
        if debug_regs.dr7 != 0 {
            unsafe {
                asm!(
                    "mov dr0, rax",
                    "mov dr1, rcx",
                    "mov dr2, rdx",
                    "mov dr3, rsi",
                    "mov dr6, r10",
                    "mov dr7, rdi",
                    in("rax") debug_regs.dr0,
                    in("rcx") debug_regs.dr1,
                    in("rdx") debug_regs.dr2,
                    in("rsi") debug_regs.dr3,
                    in("r10") debug_regs.dr6,
                    in("rdi") debug_regs.dr7,
                )
            }
        }

        unsafe {
            jmp_to_usermode(&mut cmd.gpregs);
        }

        if debug_regs.dr7 != 0 {
            unsafe {
                asm!(
                    "mov rax, dr6",
                    "mov rdx, dr7",
                    "mov dr7, rcx",
                    out("rax") debug_regs.dr6,
                    out("rdx") debug_regs.dr7,
                    in("rcx") 0,
                )
            }
        }

        unsafe {
            let component_bitmap = cmd.save_extended_registers;
            cmd.extended_regs.save_current(component_bitmap & allowed_component_bitmap);
        }

        mapper.reset_before();

        for request in cmd.memory_mappings.active().iter() {
            // SAFETY: see above
            let requested_page = unsafe { Page::from_start_address_unchecked(VirtAddr::new(request.page_start_addr())) };
            mapper.unmap_hint(requested_page);
        }

        mapper.reset_after();
    }
}