#![no_std]
#![no_main]
#![feature(custom_test_frameworks)]
#![test_runner(vmimage_x86_64::test_runner)]
#![reexport_test_harness_main = "test_main"]

use core::panic::PanicInfo;

#[no_mangle] // don't mangle the name of this function
pub extern "C" fn _start() -> ! {
    test_main();

    loop {}
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    vmimage_x86_64::test_panic_handler(info)
}
