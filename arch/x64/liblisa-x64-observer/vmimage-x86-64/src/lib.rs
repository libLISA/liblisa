// Based on: https://github.com/phil-opp/blog_os/blob/post-08/src/lib.rs

#![no_std]
#![cfg_attr(test, no_main)]
#![feature(custom_test_frameworks, abi_x86_interrupt, const_ptr_offset_from, alloc_error_handler, naked_functions, asm_sym, asm_const)]
#![feature(generic_const_exprs)]
#![test_runner(crate::test_runner)]
#![reexport_test_harness_main = "test_main"]

extern crate alloc;
use core::{panic::PanicInfo, mem::MaybeUninit};
use x86_64::instructions::port::Port;

pub mod gdt;
pub mod interrupts;
pub mod serial;
pub mod allocator;
pub mod pci;
pub mod memory;
pub mod userspace;
pub mod observer;
pub mod queue;
pub mod timer;

const HEAP_SIZE: usize = 128 * 1024; // 128KiB
static mut HEAP: [MaybeUninit<u8>; HEAP_SIZE] = [MaybeUninit::uninit(); HEAP_SIZE];

pub fn init() {
    gdt::init();
    interrupts::init_idt();
    unsafe { interrupts::PICS.lock().initialize() };
    x86_64::instructions::interrupts::enable();
    allocator::init(unsafe { &mut HEAP });
}
pub trait Testable {
    fn run(&self) -> ();
}

impl<T> Testable for T
where
    T: Fn(),
{
    fn run(&self) {
        serial_print!("{}...\t", core::any::type_name::<T>());
        self();
        serial_println!("[ok]");
    }
}

pub fn test_runner(tests: &[&dyn Testable]) {
    serial_println!("Running {} tests", tests.len());
    for test in tests {
        test.run();
    }
    exit_qemu(ExitCode::Success);
}

pub fn test_panic_handler(info: &PanicInfo) -> ! {
    serial_println!("[failed]\n");
    serial_println!("Error: {}\n", info);
    exit_qemu(ExitCode::Failed);
}

/// Exit code is reported by qemu as (value << 1) | 1
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum ExitCode {
    Success = 0x10, // 33
    Failed = 0x11, // 35
    Panic = 0x12, // 37
}

pub fn exit_qemu(exit_code: ExitCode) -> ! {
    serial_println!("Exit: {:?}", exit_code);

    let mut port = Port::new(0xf4);
    unsafe {
        port.write(exit_code as u32);
    }

    hlt_loop()
}

pub fn hlt_loop() -> ! {
    loop {
        x86_64::instructions::hlt();
    }
}

#[cfg(test)]
use bootloader_api::{entry_point, BootInfo};

#[cfg(test)]
entry_point!(test_kernel_main);

/// Entry point for `cargo xtest`
#[cfg(test)]
fn test_kernel_main(_boot_info: &'static mut BootInfo) -> ! {
    init();
    test_main();
    hlt_loop();
}

#[cfg(test)]
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    test_panic_handler(info)
}

#[alloc_error_handler]
fn alloc_error_handler(layout: alloc::alloc::Layout) -> ! {
    panic!("allocation error: {:?}", layout)
}
