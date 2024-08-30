#![no_std]
#![no_main]

use vmimage_x86_64::{exit_qemu, serial_print, serial_println, ExitCode};
use core::panic::PanicInfo;

#[no_mangle]
pub extern "C" fn _start() -> ! {
    should_fail();
    serial_println!("[test did not panic]");
    exit_qemu(ExitCode::Failed);
}

fn should_fail() {
    serial_print!("should_panic::should_fail...\t");
    assert_eq!(0, 1);
}

// #[panic_handler]
// fn panic(_info: &PanicInfo) -> ! {
//     serial_println!("[ok]");
//     exit_qemu(ExitCode::Success);
// }
