// Based on: https://github.com/phil-opp/blog_os/blob/post-08/src/gdt.rs

use lazy_static::lazy_static;
use x86_64::instructions::tables::load_tss;
use x86_64::registers::segmentation::{CS, Segment, SS, DS};
use x86_64::structures::gdt::{Descriptor, GlobalDescriptorTable, SegmentSelector, DescriptorFlags};
use x86_64::structures::tss::TaskStateSegment;
use x86_64::{VirtAddr, PrivilegeLevel};

pub const MAIN_INTERRUPT_HANDLER_IST_INDEX: u16 = 0;
pub const STACKED_INTERRUPT_HANDLER_IST_INDEX: u16 = 1;

static mut TSS: (TaskStateSegment, [u8; 16]) = (TaskStateSegment::new(), [0xff; 16]);

fn init_tss() {
    let mut tss = unsafe { &mut TSS.0 };
    const STACK_SIZE: usize = 4096 * 5;
    tss.interrupt_stack_table[MAIN_INTERRUPT_HANDLER_IST_INDEX as usize] = {
        #[used]
        static mut STACK1: [u8; STACK_SIZE] = [0; STACK_SIZE];

        let stack_start = VirtAddr::new_truncate(unsafe { &STACK1 as *const _ } as u64);
        let stack_end = stack_start + STACK_SIZE;
        stack_end
    };
    tss.interrupt_stack_table[STACKED_INTERRUPT_HANDLER_IST_INDEX as usize] = {
        #[used]
        static mut STACK2: [u8; STACK_SIZE] = [0; STACK_SIZE];

        let stack_start = VirtAddr::new_truncate(unsafe { &STACK2 as *const _ } as u64);
        let stack_end = stack_start + STACK_SIZE;
        stack_end
    };
    tss.iomap_base = unsafe { &TSS.1 as *const _ as u64 }
        .wrapping_sub(tss as *const _ as u64)
        .try_into()
        .expect("IOPRIV_BITMAP too far away");
}

lazy_static! {
    static ref GDT: (GlobalDescriptorTable, Selectors, Selectors) = {
        let mut gdt = GlobalDescriptorTable::new();
        // let code_selector = gdt.add_entry(Descriptor::kernel_code_segment());
        // let tss_selector = gdt.add_entry(Descriptor::tss_segment(&TSS));
        let kernel_data_flags = DescriptorFlags::USER_SEGMENT | DescriptorFlags::PRESENT | DescriptorFlags::WRITABLE;
        let code_selector = gdt.add_entry(Descriptor::kernel_code_segment()); // kernel code segment
        let data_selector = gdt.add_entry(Descriptor::UserSegment(kernel_data_flags.bits())); // kernel data segment
        let tss_selector = gdt.add_entry(Descriptor::tss_segment(unsafe { &TSS.0 })); // task state segment
        let user_data_selector = gdt.add_entry(Descriptor::user_data_segment()); // user data segment
        let user_code_selector = gdt.add_entry(Descriptor::user_code_segment()); // user code segment
        (
            gdt,
            Selectors {
                code: code_selector,
                data: data_selector,
                tss: tss_selector,
            },
            Selectors {
                code: user_code_selector,
                data: user_data_selector,
                tss: tss_selector,
            },
        )
    };
}

struct Selectors {
    code: SegmentSelector,
    data: SegmentSelector,
    tss: SegmentSelector,
}

pub fn init() {
    init_tss();
    GDT.0.load();
    unsafe {
        CS::set_reg(GDT.1.code);
        DS::set_reg(GDT.1.data);

        // Load a null selector into SS to prevent our interrupts from crashing.
        // iretq checks the value of SS, which must be either a valid selector or a null selector.
        // It seems the bootloader is just leaving a random value there, which is causing problems.
        SS::set_reg(SegmentSelector::new(0, x86_64::PrivilegeLevel::Ring0));
        load_tss(GDT.1.tss);
    }
}

#[inline(always)]
pub unsafe fn set_usermode_segs() -> (u16, u16) {
    // set ds and tss, return cs and ds
    let (mut cs, mut ds) = (GDT.2.code, GDT.2.data);
    cs.0 |= PrivilegeLevel::Ring3 as u16;
    ds.0 |= PrivilegeLevel::Ring3 as u16;
    DS::set_reg(ds);
    SS::set_reg(SegmentSelector::new(0, x86_64::PrivilegeLevel::Ring0));

    (cs.0, ds.0)
}
