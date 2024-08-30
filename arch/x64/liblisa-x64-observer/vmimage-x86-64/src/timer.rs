use core::arch::asm;
use x86_64::instructions::port::{Port, PortWriteOnly};

pub struct Timer {
    ch0: Port<u8>,
    ch1: Port<u8>,
    ch2: Port<u8>,
    command: PortWriteOnly<u8>,
}

pub enum AccessMode {
    LatchCountValue = 0b00,
    Lo = 0b01,
    Hi = 0b10,
    LoHi = 0b11,
}

pub enum OperatingMode {
    /// Interrupt on terminal count
    Mode0 = 0b000,
    /// Hardware re-triggerable one-shot
    Mode1 = 0b001,
    /// Rate generator
    Mode2 = 0b010,
    /// Square wave generator
    Mode3 = 0b011,
    /// Software triggered strobe
    Mode4 = 0b100,
    /// Hardware triggered strobe
    Mode5 = 0b101,
}

impl Timer {
    /// SAFETY: Allocates ports. Do not call more than once.
    pub unsafe fn init() -> Timer {
        Timer {
            ch0: Port::new(0x40),
            ch1: Port::new(0x41),
            ch2: Port::new(0x42),
            command: PortWriteOnly::new(0x43),
        }
    }

    /// The PIT runs at roughly 1193181.6666Hz
    pub fn set_ch0_reset_value(&mut self, reset_value: u16) {
        unsafe {
            // Disable interrupts while we're modifying the timer
            asm!("cli");

            self.ch0.write(reset_value as u8);
            self.ch0.write((reset_value >> 8) as u8);

            asm!("sti");
        };
    }

    pub fn configure_ch0(&mut self, mode: OperatingMode, lohi: AccessMode) {
        unsafe {
            asm!("cli");

            let channel = 0;
            self.command.write((channel as u8) << 6 | (lohi as u8) << 4 | (mode as u8) << 1);

            asm!("sti");
        }
    }
}