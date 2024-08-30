use core::cell::RefCell;

use pci_types::ConfigRegionAccess;
use x86_64::instructions::port::Port;

pub struct PciConfig {
    config_address: Port<u32>,
    config_data: Port<u32>,
}

impl PciConfig {
    pub fn new() -> PciConfig {
        PciConfig {
            config_address: Port::new(0xCF8),
            config_data: Port::new(0xCFC),
        }
    }

    pub fn read_u32(&mut self, bus: u8, slot: u8, func: u8, offset: u16) -> u32 {
        let address = ((bus as u32) << 16) | ((slot as u32) << 11) | ((func as u32) << 8) | ((offset as u32) & 0xFC) | 0x80000000;
        unsafe { 
            self.config_address.write(address); 
            self.config_data.read()
        }
    }

    pub fn write_u32(&mut self, bus: u8, slot: u8, func: u8, offset: u16, value: u32) {
        let address = ((bus as u32) << 16) | ((slot as u32) << 11) | ((func as u32) << 8) | ((offset as u32) & 0xFC) | 0x80000000;
        unsafe { 
            self.config_address.write(address); 
            self.config_data.write(value);
        }
    }
}

pub struct PciConfigAccessor(pub RefCell<PciConfig>);

impl ConfigRegionAccess for PciConfigAccessor {
    fn function_exists(&self, address: pci_types::PciAddress) -> bool {
        self.0.borrow_mut().read_u32(address.bus(), address.device(), address.function(), 0) != 0xffffffff
    }

    unsafe fn read(&self, address: pci_types::PciAddress, offset: u16) -> u32 {
        self.0.borrow_mut().read_u32(address.bus(), address.device(), address.function(), offset)
    }

    unsafe fn write(&self, address: pci_types::PciAddress, offset: u16, value: u32) {
        self.0.borrow_mut().write_u32(address.bus(), address.device(), address.function(), offset, value)
    }
}