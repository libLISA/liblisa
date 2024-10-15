#![no_std]
#![no_main]
#![feature(custom_test_frameworks)]
#![test_runner(vmimage_x86_64::test_runner)]
#![reexport_test_harness_main = "test_main"]

extern crate alloc;

use alloc::vec::Vec;
use bootloader_api::config::Mapping;
use bootloader_api::info::MemoryRegionKind;
use pci_types::{PciHeader, PciAddress, EndpointHeader, Bar};
use bootloader_api::{entry_point, BootInfo, BootloaderConfig};
use liblisa_x64_observer_shmqueue::frame::command::{Permissions, MemoryMapping, CommandFrame, ExtendedRegs};
use liblisa_x64_observer_shmqueue::frame::control::{ControlFrameData, ClientInfo, Layout, LayoutEntry};
use liblisa_x64_observer_shmqueue::regs::{GpRegs, YmmRegs};
use vmimage_x86_64::interrupts::reset_timer;
use vmimage_x86_64::observer::{Observer, ObservationMapper};
use vmimage_x86_64::queue::{Incoming, PageOffsetTranslator};
use vmimage_x86_64::timer::{Timer, AccessMode, OperatingMode};
use x86_64::registers::control::{Cr4, Cr4Flags, Cr0, Cr0Flags};
use x86_64::registers::xcontrol::{XCr0, XCr0Flags};
use x86_64::{PhysAddr, VirtAddr};
use x86_64::structures::paging::{PageTableFlags, PhysFrame};
use core::arch::asm;
use core::mem::MaybeUninit;
use core::sync::atomic::Ordering;
use core::{panic::PanicInfo, cell::RefCell};
use vmimage_x86_64::{serial_println, exit_qemu, ExitCode};
use vmimage_x86_64::memory::{ContiguousFrameAllocator, PageMapper, UserPageMapper};
use vmimage_x86_64::pci::*;
use liblisa_x64_observer_shmqueue::queue::Queue;

pub static BOOTLOADER_CONFIG: BootloaderConfig = {
    let mut config = BootloaderConfig::new_default();
    config.kernel_stack_size = 0x18000;
    config.mappings.aslr = false;

    config.mappings.framebuffer = Mapping::FixedAddress(0xe000_000_000);
    config.mappings.physical_memory = Some(Mapping::FixedAddress(0x20_000_000_000));
    config.mappings.boot_info = Mapping::FixedAddress(0x00001eecb3619000);
    config.mappings.kernel_stack = Mapping::FixedAddress(0x00001eecb3600000);
    // config.mappings.dynamic_range_start = Some(0x00001eecb3620000);
    // config.mappings.dynamic_range_end = Some(0x00001eecb4600000);

    config
};

entry_point!(kernel_main, config = &BOOTLOADER_CONFIG);

/// Returns (eax, r11, ecx, edx) returned by the cpuid instruction
fn cpuid(function: u32, subfunction: u32) -> (u32, u32, u32, u32) {
    let r1;
    let r2;
    let r3;
    let r4;
    unsafe {
        asm!(
            "mov r11, 1234321",
            "push rbx",
            "cpuid",
            "mov r11, rbx",
            "pop rbx",
            inout("eax") function => r1,
            out("r11") r2,
            inout("ecx") subfunction => r3,
            out("edx") r4,
        )
    }

    (r1, r2, r3, r4)
}

fn tsc() -> u64 {
    let hi: u64;
    let lo: u64;
    unsafe {
        asm!(
            "rdtsc",
            out("rax") lo,
            out("rdx") hi,
        );
    }

    (hi << 32) | lo
}

fn find_memory_mapped_range() -> Option<(PhysAddr, usize)> {
    let access = PciConfigAccessor(RefCell::new(PciConfig::new()));
    let ivshmem_id = (0x1af4, 0x1110);
    for bus in 0..=255 {
        for device in 0..32 {
            let address = PciAddress::new(0, bus, device, 0);
            let header = PciHeader::new(address);
            let (vendor_id, device_id) = header.id(&access);
            if (vendor_id, device_id) == ivshmem_id {
                serial_println!("Found ivshmem device at {:X?}", address);
                let endpoint = EndpointHeader::from_header(header, &access).unwrap();
                let (revision, _, _, _) = endpoint.header().revision_and_class(&access);

                assert_eq!(revision, 1, "only rev. 1 of the ivshmem device is supported, you have rev. {}", revision);

                let bar = endpoint.bar(2, &access).unwrap();
                serial_println!("Bar: {:?}", bar);

                let (bar_physical_address, bar_size) = match bar {
                    Bar::Memory64 { address, size, .. } => (address, size),
                    _ => panic!("expected ivshmem to provide a Memory64 BAR"),
                };

                serial_println!("BAR at 0x{:x}-0x{:x} (physical address)", bar_physical_address, bar_physical_address + bar_size);

                return Some((PhysAddr::new(bar_physical_address), bar_size as usize));
            }
        }
    }

    None
}

struct ObsMapper {
    translator: PageOffsetTranslator,
    bar_base: PhysAddr,
    mapper: UserPageMapper,
    qemu_cache_invalidate: bool,
}

impl ObservationMapper for ObsMapper {
    fn map(&mut self, frame_index: usize, page: x86_64::structures::paging::Page, permissions: Permissions) {
        let page_offset = self.translator.page_offset(frame_index);
        let phys_addr = self.bar_base + page_offset;
        let frame = PhysFrame::from_start_address(phys_addr).unwrap();

        self.mapper.map_user_direct(frame, page, match permissions {
            Permissions::Executable => PageTableFlags::empty(),
            // TODO: Check if we have the feature enabled for NX pages in the EFER register
            Permissions::Read => PageTableFlags::NO_EXECUTE,
            Permissions::ReadWrite => PageTableFlags::NO_EXECUTE | PageTableFlags::WRITABLE,
        });
    }

    fn map_executable(&mut self, frame_index: usize, page: x86_64::structures::paging::Page, addr: u64, permissions: Permissions) {
        let page_offset = self.translator.page_offset(frame_index);
        let phys_addr = self.bar_base + page_offset;
        let frame = PhysFrame::from_start_address(phys_addr).unwrap();
        if self.qemu_cache_invalidate && permissions == Permissions::Executable {
            let addr = if addr >= page.start_address().as_u64() && addr <= page.start_address().as_u64() + 4095 {
                addr
            } else {
                page.start_address().as_u64()
            };
            
            self.mapper.map_user_direct(frame, page, PageTableFlags::WRITABLE);

            unsafe {
                let addr = if addr == 0 {
                    1
                } else {
                    addr
                } as *mut u8;
                let v = core::ptr::read_volatile(addr);
                core::ptr::write_volatile(addr, v);
            }
        }

        self.mapper.map_user_direct(frame, page, PageTableFlags::empty());
    }

    fn unmap_hint(&mut self, page: x86_64::structures::paging::Page) {
        self.mapper.unmap_hint(page)
    }

    fn reset_before(&mut self) {
        self.mapper.reset_before()
    }

    fn reset_after(&mut self) {
        self.mapper.reset_after()
    }

    fn ready_hint(&mut self) {
        
    }
}

fn kernel_main(boot_info: &'static mut BootInfo) -> ! {
    vmimage_x86_64::init();
    let mut timer = unsafe { Timer::init() };
    // somewhere around 1.2KHz
    timer.configure_ch0(OperatingMode::Mode2, AccessMode::LoHi);
    timer.set_ch0_reset_value(0x2000);

    let physical_memory_offset = boot_info.physical_memory_offset.into_option().unwrap();
    let phys_mem_offset = VirtAddr::new(physical_memory_offset);

    serial_println!("rip = 0x{0:x} = {0:064b}", x86_64::registers::read_rip());
    serial_println!("physical memory offset = 0x{0:x}", physical_memory_offset);

    serial_println!("{} memory regions", boot_info.memory_regions.len());

    for region in boot_info.memory_regions.iter() {
        serial_println!("Memory region 0x{:x} - 0x{:x}: {:?}", region.start, region.end, region.kind);
    }

    let allocator_region = boot_info.memory_regions.iter()
        .filter(|r| r.kind == MemoryRegionKind::Usable)
        .max_by_key(|r| r.end - r.start)
        .unwrap();
    
    serial_println!("Using physical memory 0x{:x}-0x{:x} for frame allocation", allocator_region.start, allocator_region.end);

    let frame_allocator = ContiguousFrameAllocator::new(PhysAddr::new(allocator_region.start), PhysAddr::new(allocator_region.end));

    // {
    //     let mut mapper = unsafe { memory::init(phys_mem_offset) };
    //     memory::print_page_table(&mut mapper.level_4_table(), phys_mem_offset, 0, 4);
    // }

    let mut mapper = unsafe { PageMapper::init(phys_mem_offset, frame_allocator, 0x00001eecb3600000) };
    

    serial_println!("Sucessfully switched page tables!");
    serial_println!();
    serial_println!();

    const UMIP_SUPPORT: u32 = 1 << 2;
    let (_, _, feature_identifiers, _) = cpuid(0x07, 0x00);
    let umip_supported = feature_identifiers & UMIP_SUPPORT != 0;

    const XSAVE_SUPPORT: u32 = 1 << 26;
    const SSE_SUPPORT: u32 = 1 << 25;
    const AVX_SUPPORT: u32 = 1 << 28;
    let (_, _, feature_identifiers, extra) = cpuid(0x01, 0);
    let xsave = feature_identifiers & XSAVE_SUPPORT != 0;
    let sse = extra & SSE_SUPPORT != 0;
    let avx = feature_identifiers & AVX_SUPPORT != 0;

    // XSAVE was introduced on Intel CPUs in 2008.
    // Virtualisation support was added on Intel in 2005 and AMD 2006.
    // There's only 3 years of CPUs that would be able to run this observer, but would not support XSAVE.
    // It should be relatively easy to support FXSAVE as well, but that currently isn't a priority. 
    serial_println!("CPU features: {:032b} [xsave={:?}]", feature_identifiers, xsave);
    if !xsave {
        panic!("Only the newer XSAVE is supported. Older F(X/N)SAVE are not implemented.");
    }

    serial_println!("Enabling x87 exceptions");
    unsafe {
        // Enable x87 exceptions
        Cr0::update(|f| {
            f.set(Cr0Flags::NUMERIC_ERROR, true);
        });
    }

    if sse {
        serial_println!("Enabling SSE (cr0)");
        // Enable SSE
        unsafe {
            Cr0::update(|f| {
                f.set(Cr0Flags::EMULATE_COPROCESSOR, false);
                f.set(Cr0Flags::MONITOR_COPROCESSOR, true);
            });
        }

        serial_println!("Enabling SSE (cr4)");
        unsafe {
            Cr4::update(|f| {
                f.set(Cr4Flags::OSFXSR, true);
                f.set(Cr4Flags::OSXMMEXCPT_ENABLE, true);
            });
        }
    }

    if umip_supported {
        serial_println!("Enabling UMIP");
        unsafe {
            Cr4::update(|f| {
                f.set(Cr4Flags::USER_MODE_INSTRUCTION_PREVENTION, true);
            });
        }
    }

    serial_println!("Checking supported feature masks");
    let (xfeature_supported_mask1, current_size, max_size, xfeature_supported_mask2) = cpuid(0x0d, 0);
    let xfeature_supported_mask = xfeature_supported_mask1 as u64 | ((xfeature_supported_mask2 as u64) << 32);

    let fp_mmx = xfeature_supported_mask & 0b001 != 0;
    let sse = xfeature_supported_mask & 0b010 != 0;
    let extended_sse = xfeature_supported_mask & 0b100 != 0;
    serial_println!("XSAVE supports: fp_mmx={:?}, sse={:?}, extended_sse={:?}", fp_mmx, sse, extended_sse);
    serial_println!("XSAVE current size: {} / {}; Features: {:064b}", current_size, max_size, xfeature_supported_mask);

    // Enable XGETBV/XSETBV
    unsafe { Cr4::update(|f| f.set(Cr4Flags::OSXSAVE, true)); }

    // Enable x87/mmx, basic SSE and AVX (up to AVX-256)
    unsafe {
        if sse && avx {
            XCr0::write(XCr0Flags::X87 | XCr0Flags::SSE | XCr0Flags::AVX)
        } else if sse {
            XCr0::write(XCr0Flags::X87 | XCr0Flags::SSE)
        } else {
            XCr0::write(XCr0Flags::X87)
        }
    };

    serial_println!("New XCr0 value: {:?}", XCr0::read());

    let (_, current_size, max_size, _) = cpuid(0x0d, 0);
    serial_println!("XSAVE current size: {} / {}", current_size, max_size);

    // TODO: Can we request this via cpuid as well?
    let fp_xmm_offset = 0;
    let fp_xmm_size = 512;
    let header_offset = 512;
    let header_size = 64;

    let (avx_size, avx_offset, _, _) = cpuid(0xd, 2);

    serial_println!("XSAVE layout:");
    serial_println!("@{:4}: fp/xmm  {:3}b", fp_xmm_offset, fp_xmm_size);
    serial_println!("@{:4}: header  {:3}b", header_offset, header_size);
    serial_println!("@{:4}: avx-256 {:3}b", avx_offset, avx_size);

    let layout = Layout {
        x87: LayoutEntry {
            available: true,
            offset: fp_xmm_offset,
            size: fp_xmm_size,
        },
        // LayoutEntry {
        //     kind: LayoutKind::XsaveHeader,
        //     offset: header_offset,
        //     size: header_size,
        // },
        avx256: LayoutEntry {
            available: avx,
            offset: avx_offset as u64,
            size: avx_size as u64,
        },
    };

    let mut exregs = ExtendedRegs::new();
    unsafe {
        // Make sure the floating point registers aren't completely empty by pushing +1.0 on the stack.
        if avx {
            asm!(
                "FLD1",
                "cvtsi2sd xmm3, rsp",
                "vcmptrueps ymm0, ymm0, ymm0",
            );
        }

        // Load a null LDT segment, so all instructions using the LDT will cause a #GP
        asm!(
            "LLDT ax",
            in("ax") 0,
        );
    }

    unsafe { exregs.save_current(0b111) }

    serial_println!("{:X?}", exregs.legacy_area());
    serial_println!("{:X?}", exregs.header());
    serial_println!("{:X?}", unsafe { exregs.component::<YmmRegs>(avx_offset as usize) });

    let mut observer = Observer::new();
    let (bar_start, bar_size) = find_memory_mapped_range().expect("ivshmem device is missing");
    let bar_virt_addr = mapper.map_physical_range(bar_start, bar_size);
    serial_println!("BAR has been mapped into memory @ {:X}", bar_virt_addr);

    let mut extra_page = mapper.allocate_new_page();
    let mapper = mapper.freeze();

    // Initialize the control frame
    let mut control_frames = Vec::new();
    unsafe {
        let mut control_frame_addr = bar_virt_addr;
        loop {
            let client_info = control_frame_addr.as_mut_ptr::<u8>()
                .wrapping_add(memoffset::offset_of!(ControlFrameData, client_info))
                as *mut MaybeUninit<ClientInfo>;
            
            (*client_info).write(ClientInfo {
                reserved_start: mapper.reserved_range().start.as_u64(),
                reserved_end: mapper.reserved_range().end.as_u64(),
            });

            let xsave_layout = control_frame_addr.as_mut_ptr::<u8>()
                .wrapping_add(memoffset::offset_of!(ControlFrameData, xsave_layout))
                as *mut MaybeUninit<Layout>;

            (*xsave_layout).write(layout.clone());

            // SAFETY: The host has initialized most of the control frame.
            // We initialized the client_info field above.
            // Therefore the entire control frame is initalized, and we can create a reference to it.
            let ptr = control_frame_addr.as_mut_ptr() as *mut ControlFrameData;
            let size = ((*ptr).num_command_frames + 1) * 4096;

            control_frames.push((control_frame_addr, size));

            let next_control_frame = (*ptr).next_control_frame;
            if next_control_frame == 0 {
                break;
            } else {
                control_frame_addr = bar_virt_addr + next_control_frame as u64;
            }
        }
    }

    for (control_frame_addr, _) in control_frames.iter_mut().rev() {
        unsafe {
            let ptr = control_frame_addr.as_mut_ptr() as *mut ControlFrameData;
            (*ptr).current.store(0, Ordering::Release);
        }
    }

    serial_println!("Control frame initialized");

    let mut queues = control_frames.into_iter().map(|(addr, size)| unsafe {
        Queue::new(addr.as_mut_ptr(), size as usize)
    }).collect::<Vec<_>>();

    serial_println!("Resetting timer");
    reset_timer();

    let allowed_component_bitmap = 0b1 | (sse as u64) << 1 | (avx as u64) << 2;
    
    match Incoming::new(&mut queues) {
        Ok(mut queue) => {
            let translator = queue.offset_translator();
            let mut obs_mapper = ObsMapper {
                qemu_cache_invalidate: true,
                translator,
                bar_base: bar_start,
                mapper,
            };

            serial_println!("Waiting for command");
        
            let mut num_waiting: u64 = 0;
            loop {
                // serial_println!("Checking command...");
                if let Some(cmd) = queue.receive_request() {
                    num_waiting = 0;
                    // serial_println!("Received observation request: {:X?}", cmd.gpregs);
                    reset_timer();
                    
                    observer.observe(&mut obs_mapper, allowed_component_bitmap, cmd);
        
                    queue.mark_processed();
                    // serial_println!("Observation request done!");
                } else {
                    // serial_println!("Waiting!");
                    // We busy-wait for 50K so latency doesn't get too high if observations are requested one-by-one.
                    if num_waiting > 50_000 {
                        // Wait until the next timer tick
                        unsafe {
                            asm!(
                                "sti",
                                "hlt",
                            );
                        }
                    } else {
                        num_waiting += 1;
                        // signal to the CPU that we're in a busy loop; should help with SMT/HT
                        unsafe {
                            asm!("pause");
                        }
                    }
                }
            }
        }
        Err(()) => {
            serial_println!("Shared memory is not set up correctly.");
            serial_println!("Starting self-benchmark");


            const NUM_MEASUREMENTS: usize = 100;

            #[cfg(not(debug_assertions))]
            const NUM_ITERATIONS: usize = 1_000_000;
            #[cfg(debug_assertions)]
            const NUM_ITERATIONS: usize = 100;
        
        
            const ADDRESS1: u64 = 0x4321000;
            const ADDRESS2: u64 = 0x54321000;
        
            
            unsafe { extra_page.write(0, &[ 0xcc ]) }
            // let mut code = [ 0xCC ];
            // let mut memory1 = [
            //     MapRequest::new(VirtAddr::new(ADDRESS), &mut code, Permissions::Executable),
            // ];
        
            // let mut code = [ 0xCC ];
            // let mut a = [ 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3 ];
            // let mut b = [ 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3 ];
            // let mut c = [ 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3 ];
            // let mut d = [ 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3 ];
            // let mut memory2 = [
            //     MapRequest::new(VirtAddr::new(ADDRESS), &mut code, Permissions::Executable),
            //     MapRequest::new(VirtAddr::new(0x11223344), &mut a, Permissions::Executable),
            //     MapRequest::new(VirtAddr::new(0x11323344), &mut b, Permissions::Executable),
            //     MapRequest::new(VirtAddr::new(0x11423344), &mut c, Permissions::Executable),
            //     MapRequest::new(VirtAddr::new(0x11523344), &mut d, Permissions::Executable),
            // ];
            let mut regs = GpRegs::default();
            let mut obs_mapper = OffsetObsMapper {
                base: extra_page.physical_address,
                mapper,
            };

            serial_println!("Begin benchmark!");
            let mut measurements = [0u64; NUM_MEASUREMENTS];
            for (index, m) in measurements.iter_mut().enumerate() {
                let requests1 = &[MemoryMapping::new(ADDRESS1, 0, Permissions::Executable)];
                let requests2 = &[MemoryMapping::new(ADDRESS2, 0, Permissions::Executable)];
                let start = tsc();
                for _i in 0..NUM_ITERATIONS/2 {
                    // serial_println!("{}", _i);
                    regs.rip = ADDRESS1;
                    let mut frame = CommandFrame::new(regs.clone(), requests1.iter().cloned());
                    reset_timer();
                    observer.observe(&mut obs_mapper, allowed_component_bitmap, &mut frame);
            
                    regs.rip = ADDRESS2;
                    let mut frame = CommandFrame::new(regs.clone(), requests2.iter().cloned());
                    reset_timer();
                    observer.observe(&mut obs_mapper, allowed_component_bitmap, &mut frame);
            
                    // serial_println!("Regs after: {:#X?}", regs);
                }
                let delta = tsc().checked_sub(start).unwrap_or(0);
                *m = delta;

                serial_println!("[measurement {:3}] That took {} cycles", index, delta);
                serial_println!("                    That's {} cycles/observation (guessing {}ns/observation)", delta / NUM_ITERATIONS as u64, delta / NUM_ITERATIONS as u64 / 4);
            }

            let avg = measurements.iter().copied().sum::<u64>() / NUM_MEASUREMENTS as u64;
            let variance = measurements.iter().map(|&m| (m.max(avg) - m.min(avg)) * (m.max(avg) - m.min(avg))).sum::<u64>() / NUM_MEASUREMENTS as u64;
            let stddev = primitive_sqrt(variance);

            let avg_per_observation = avg / NUM_ITERATIONS as u64;
            serial_println!("Average : {} cycles/observation", avg_per_observation);
            let stddev_per_observation = stddev / NUM_ITERATIONS as u64;
            serial_println!("Variance: {} cycles/observation", stddev_per_observation);

            serial_println!("Benchmark result: {}-{} cycles/observation", avg_per_observation - stddev_per_observation, avg_per_observation + stddev_per_observation);
        
            serial_println!("Done!");
        }
    }

    #[cfg(test)]
    test_main();

    exit_qemu(ExitCode::Success);
}

fn primitive_sqrt(val: u64) -> u64 {
    for n in 0.. {
        if n * n >= val {
            return n;
        }
    }

    unreachable!()
}

struct OffsetObsMapper {
    base: PhysAddr,
    mapper: UserPageMapper,
}

impl ObservationMapper for OffsetObsMapper {
    #[inline]
    fn map(&mut self, frame_index: usize, page: x86_64::structures::paging::Page, permissions: Permissions) {
        let page_offset = frame_index * 4096;
        let phys_addr = self.base + page_offset;
        let frame = PhysFrame::from_start_address(phys_addr).unwrap();
        self.mapper.map_user_direct(frame, page, match permissions {
            Permissions::Executable => PageTableFlags::empty(),
            // TODO: Check if we have the feature enabled for NX pages in the EFER register
            Permissions::Read => PageTableFlags::NO_EXECUTE,
            Permissions::ReadWrite => PageTableFlags::NO_EXECUTE | PageTableFlags::WRITABLE,
        });
    }

    fn map_executable(&mut self, frame_index: usize, page: x86_64::structures::paging::Page, _addr: u64, permissions: Permissions) {
        self.map(frame_index, page, permissions);
    }

    #[inline]
    fn unmap_hint(&mut self, page: x86_64::structures::paging::Page) {
        self.mapper.unmap_hint(page)
    }

    #[inline]
    fn reset_before(&mut self) {
        self.mapper.reset_before()
    }

    #[inline]
    fn reset_after(&mut self) {
        self.mapper.reset_after()
    }

    #[inline]
    fn ready_hint(&mut self) { }
}

/// This function is called on panic.
#[cfg(not(test))]
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    serial_println!("{}", info);
    exit_qemu(ExitCode::Panic);
}

#[cfg(test)]
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    vmimage_x86_64::test_panic_handler(info)
}

#[test_case]
fn trivial_assertion() {
    assert_eq!(1, 1);
}
