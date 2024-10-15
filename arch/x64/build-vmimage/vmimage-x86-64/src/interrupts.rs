use core::{arch::naked_asm, sync::atomic::{AtomicU32, Ordering}};
use crate::{gdt, hlt_loop, serial_println, serial_print};
use lazy_static::lazy_static;
use pic8259::ChainedPics;
use x86_64::{structures::idt::{InterruptDescriptorTable, InterruptStackFrame, PageFaultErrorCode}, PrivilegeLevel, VirtAddr};

pub const PIC_1_OFFSET: u8 = 32;
pub const PIC_2_OFFSET: u8 = PIC_1_OFFSET + 8;

#[derive(Debug, Clone, Copy)]
#[repr(u8)]
pub enum InterruptIndex {
    Timer = PIC_1_OFFSET,
    Keyboard,
}

impl InterruptIndex {
    fn as_u8(self) -> u8 {
        self as u8
    }

    fn as_usize(self) -> usize {
        usize::from(self.as_u8())
    }
}

pub static PICS: spin::Mutex<ChainedPics> =
    spin::Mutex::new(unsafe { ChainedPics::new(PIC_1_OFFSET, PIC_2_OFFSET) });

lazy_static! {
    static ref IDT: InterruptDescriptorTable = {
        let mut idt = InterruptDescriptorTable::new();
        unsafe {
            idt[InterruptIndex::Keyboard.as_usize()]
                .set_handler_fn(keyboard_interrupt_handler)
                .set_stack_index(gdt::MAIN_INTERRUPT_HANDLER_IST_INDEX);

            // 0
            idt.divide_error
                .set_handler_addr(VirtAddr::new((divide_error as *const ()) as u64))
                .set_stack_index(gdt::MAIN_INTERRUPT_HANDLER_IST_INDEX);
            // 1
            idt.debug
                .set_handler_addr(VirtAddr::new((debug_handler as *const ()) as u64))
                .set_stack_index(gdt::MAIN_INTERRUPT_HANDLER_IST_INDEX);
            // 2: non-maskable interrupt
            // 3: breakpoint
            idt.breakpoint
                .set_handler_addr(VirtAddr::new((breakpoint_handler as *const ()) as u64))
                .set_stack_index(gdt::MAIN_INTERRUPT_HANDLER_IST_INDEX)
                .set_privilege_level(PrivilegeLevel::Ring3);
            // 4: overflow
            idt.invalid_opcode
                .set_handler_addr(VirtAddr::new((overflow_handler as *const ()) as u64))
                .set_stack_index(gdt::MAIN_INTERRUPT_HANDLER_IST_INDEX);
            // 5: bounds range exceeded
            idt.invalid_opcode
                .set_handler_addr(VirtAddr::new((bounds_handler as *const ()) as u64))
                .set_stack_index(gdt::MAIN_INTERRUPT_HANDLER_IST_INDEX);
            // 6: invalid opcode
            idt.invalid_opcode
                .set_handler_addr(VirtAddr::new((invalid_opcode_handler as *const ()) as u64))
                .set_stack_index(gdt::MAIN_INTERRUPT_HANDLER_IST_INDEX);
            // TODO (maybe?) 7: device not available
            // 8: double fault
            idt.double_fault
                .set_handler_fn(kernel_double_fault_handler)
                .set_stack_index(gdt::MAIN_INTERRUPT_HANDLER_IST_INDEX);
            // 9: coprocessor segment overrun
            // TODO (maybe?) 10: invalid tss
            idt.invalid_tss
                .set_handler_fn(invalid_tss)
                .set_stack_index(gdt::MAIN_INTERRUPT_HANDLER_IST_INDEX);
            // 11: segment not present
            idt.segment_not_present
                .set_handler_addr(VirtAddr::new((segment_not_present_handler as *const ()) as u64))
                .set_stack_index(gdt::MAIN_INTERRUPT_HANDLER_IST_INDEX);
            // 12: stack segment fault
            idt.stack_segment_fault
                .set_handler_addr(VirtAddr::new((stack_segment_fault_handler as *const ()) as u64))
                .set_stack_index(gdt::MAIN_INTERRUPT_HANDLER_IST_INDEX);
            // 13: general protection fault
            idt.general_protection_fault
                .set_handler_addr(VirtAddr::new((general_protection_fault_handler as *const ()) as u64))
                .set_stack_index(gdt::MAIN_INTERRUPT_HANDLER_IST_INDEX);
            // 14: page fault
            idt.page_fault
                .set_handler_addr(VirtAddr::new((page_fault_handler as *const ()) as u64))
                .set_stack_index(gdt::MAIN_INTERRUPT_HANDLER_IST_INDEX);
            // 15: reserved
            // 16: floating-point exception
            idt.x87_floating_point
                .set_handler_addr(VirtAddr::new((floating_point_exception_handler as *const ()) as u64))
                .set_stack_index(gdt::MAIN_INTERRUPT_HANDLER_IST_INDEX);
            // TODO 17: alignment check
            // TODO 18: machine check
            // 19: SIMD FP exception
            idt.simd_floating_point
                .set_handler_addr(VirtAddr::new((simd_floating_point_exception_handler as *const ()) as u64))
                .set_stack_index(gdt::MAIN_INTERRUPT_HANDLER_IST_INDEX);
            // 20: virtualisation exception
            // 21: control protection exception
            // 22-27: reserved
            // 28: hypervisor injection exception
            // 29: vmm communication exception
            // 30: security exception
            // 31: reserved

            idt[InterruptIndex::Timer.as_usize()]
                .set_handler_addr(VirtAddr::new((timer_interrupt_handler as *const ()) as u64))
                .set_stack_index(gdt::STACKED_INTERRUPT_HANDLER_IST_INDEX);
        }
        idt
    };
}

pub fn init_idt() {
    IDT.load();
}

crate::generate_interrupt_entry!(0: divide_error => kernel_divide_error);
extern "x86-interrupt" fn kernel_divide_error(stack_frame: InterruptStackFrame) {
    panic!("Exception: Divide Error\n{:#?}", stack_frame);
}

crate::generate_interrupt_entry!(1: debug_handler);
crate::generate_interrupt_entry!(3: breakpoint_handler);

crate::generate_interrupt_entry!(4: overflow_handler => kernel_overflow_handler);
extern "x86-interrupt" fn kernel_overflow_handler(stack_frame: InterruptStackFrame) {
    panic!("Exception: Overflow\n{:#?}", stack_frame);
}

crate::generate_interrupt_entry!(5: bounds_handler => kernel_bounds_handler);
extern "x86-interrupt" fn kernel_bounds_handler(stack_frame: InterruptStackFrame) {
    panic!("Exception: Bounds\n{:#?}", stack_frame);
}

crate::generate_interrupt_entry!(6: invalid_opcode_handler => kernel_invalid_opcode_handler);
extern "x86-interrupt" fn kernel_invalid_opcode_handler(stack_frame: InterruptStackFrame) {
    panic!("Exception: Invalid Opcode\n{:#?}", stack_frame);
}

extern "x86-interrupt" fn kernel_double_fault_handler(
    stack_frame: InterruptStackFrame,
    _error_code: u64,
) -> ! {
    panic!("Exception: Double Fault\n{:#?}", stack_frame);
}

crate::generate_interrupt_entry!(11(with_error=u64): segment_not_present_handler => kernel_segment_not_present_handler);
extern "x86-interrupt" fn kernel_segment_not_present_handler(
    stack_frame: InterruptStackFrame,
    _error_code: u64,
) {
    panic!("Exception: Segment not present\n{:#?}", stack_frame);
}

crate::generate_interrupt_entry!(12(with_error=u64): stack_segment_fault_handler => kernel_stack_segment_fault_handler);
extern "x86-interrupt" fn kernel_stack_segment_fault_handler(
    stack_frame: InterruptStackFrame,
    _error_code: u64,
) {
    panic!("Exception: Stack segment fault\n{:#?}", stack_frame);
}

crate::generate_interrupt_entry!(13(with_error=u64): general_protection_fault_handler => kernel_general_protection_fault);
extern "x86-interrupt" fn kernel_general_protection_fault(
    stack_frame: InterruptStackFrame,
    error_code: u64,
) {
    if error_code != 0 {
        let e = error_code & 0b1;
        let tbl = (error_code >> 1) & 0b11;
        let index = (error_code >> 3) & 0b1_1111_1111_1111;

        const TABLES: &[&'static str] = &[ "GDT", "IDT", "LDT", "IDT" ];
        serial_println!("There is a problem with {}table {} ({}), index {}", 
            if e == 1 { "external " } else { "" }, 
            TABLES[tbl as usize], tbl, 
            index
        );
    }

    panic!("Exception: General protection fault ({}) \n{:#?}", error_code, stack_frame);
}

crate::generate_interrupt_entry!(14(with_error=PageFaultErrorCode): page_fault_handler => kernel_page_fault_handler);
extern "x86-interrupt" fn kernel_page_fault_handler(
    stack_frame: InterruptStackFrame,
    error_code: PageFaultErrorCode,
) {
    use x86_64::registers::control::Cr2;

    serial_println!("EXCEPTION: PAGE FAULT");
    serial_println!("Accessed Address: {:?}", Cr2::read());
    serial_println!("Error Code: {:?}", error_code);
    serial_println!("{:#?}", stack_frame);
    hlt_loop();
}

crate::generate_interrupt_entry!(16: floating_point_exception_handler => kernel_floating_point_exception_handler);
extern "x86-interrupt" fn kernel_floating_point_exception_handler(stack_frame: InterruptStackFrame) {
    panic!("Exception: Floating point\n{:#?}", stack_frame);
}

crate::generate_interrupt_entry!(19: simd_floating_point_exception_handler => kernel_simd_floating_point_exception_handler);
extern "x86-interrupt" fn kernel_simd_floating_point_exception_handler(stack_frame: InterruptStackFrame) {
    panic!("Exception: SIMD Floating point\n{:#?}", stack_frame);
}

extern "x86-interrupt" fn kernel_timer_interrupt_handler(_stack_frame: InterruptStackFrame) {
    HANG_COUNTER.fetch_add(1, Ordering::SeqCst);

    unsafe {
        PICS.lock()
            .notify_end_of_interrupt(InterruptIndex::Timer.as_u8());
    }
}

static HANG_COUNTER: AtomicU32 = AtomicU32::new(0);

pub fn reset_timer() {
    HANG_COUNTER.store(0, Ordering::SeqCst)
}

pub fn get_timer() -> u32 {
    HANG_COUNTER.load(Ordering::SeqCst)
}

extern "C" fn check_timer_interrupt() -> bool {
    let timeout = HANG_COUNTER.fetch_add(1, Ordering::SeqCst) >= 100;

    unsafe {
        PICS.lock()
            .notify_end_of_interrupt(InterruptIndex::Timer.as_u8());
    }

    timeout
}

#[naked]
unsafe extern "C" fn timer_interrupt_handler() {
    naked_asm!(
        // If we're currently not in userspace, bail out to the kernel handler
        "cmp qword ptr [rip + {RESTORE_STATE}], 0",
        "jnz 3f",
        "jmp {kernel_handler}",

        "3:",
        "push rax",
        "push rcx",
        "push rdx",
        "push rsi",
        "push rdi",
        "push r8",
        "push r9",
        "push r10",
        "push r11",
        "cld",

        "call {check_timer_interrupt}",
        "pop r11",
        "pop r10",
        "pop r9",
        "pop r8",
        "pop rdi",
        "pop rsi",
        "pop rdx",
        "pop rcx",

        "test al, al",
        "jnz 4f",

        // Counter didn't expire, continue execution
        "pop rax",
        "iretq",
        
        // Counter expired, trigger exception
        "4:",
        "pop rax",
        "push 0",
        "push {id}",
        "jmp {c}",

        id = const 0xffffffff_ffffffffu64,
        kernel_handler = sym kernel_timer_interrupt_handler,
        c = sym crate::userspace::handle_interrupt,
        check_timer_interrupt = sym check_timer_interrupt,
        RESTORE_STATE = sym crate::userspace::RESTORE_STATE,
    )
}

extern "x86-interrupt" fn invalid_tss(
    stack_frame: InterruptStackFrame,
    _error_code: u64,
) {
    panic!("Exception: Invalid TSS\n{:#?}", stack_frame);
}

extern "x86-interrupt" fn keyboard_interrupt_handler(_stack_frame: InterruptStackFrame) {
    use pc_keyboard::{layouts, DecodedKey, HandleControl, Keyboard, ScancodeSet1};
    use spin::Mutex;
    use x86_64::instructions::port::Port;

    lazy_static! {
        static ref KEYBOARD: Mutex<Keyboard<layouts::Us104Key, ScancodeSet1>> = Mutex::new(
            Keyboard::new(layouts::Us104Key, ScancodeSet1, HandleControl::Ignore)
        );
    }

    let mut keyboard = KEYBOARD.lock();
    let mut port = Port::new(0x60);

    let scancode: u8 = unsafe { port.read() };
    if let Ok(Some(key_event)) = keyboard.add_byte(scancode) {
        if let Some(key) = keyboard.process_keyevent(key_event) {
            match key {
                DecodedKey::Unicode(character) => serial_print!("{}", character),
                DecodedKey::RawKey(key) => serial_print!("{:?}", key),
            }
        }
    }

    unsafe {
        PICS.lock()
            .notify_end_of_interrupt(InterruptIndex::Keyboard.as_u8());
    }
}

#[test_case]
fn test_breakpoint_exception() {
    // invoke a breakpoint exception
    x86_64::instructions::interrupts::int3();
}
