use std::arch::asm;
use std::collections::VecDeque;
use std::fs;
use std::io::{self, Read};
use std::iter::{once, Fuse};
use std::mem::ManuallyDrop;
use std::ops::{Index, Range};
use std::os::unix::prelude::CommandExt;
use std::process::{Child, Command, ExitStatus, Stdio};
use std::rc::Rc;
use std::sync::atomic::Ordering;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use liblisa_x64_observer_shmqueue::frame::command::{CommandFrame, MemoryMapping, MemoryMappings};
pub use liblisa_x64_observer_shmqueue::frame::command::{ExtendedRegs, Permissions};
use liblisa_x64_observer_shmqueue::frame::control::{make_atomic_u32, ControlFrame, ControlFrameData, Host, Layout};
use liblisa_x64_observer_shmqueue::frame::FRAME_SIZE;
use liblisa_x64_observer_shmqueue::queue::Queue;
pub use liblisa_x64_observer_shmqueue::regs::{DebugRegs, GpRegs, St, XsaveLegacyArea, YmmRegs};
use nix::sched::CpuSet;
use nix::unistd::Pid;
use rand::distributions::Alphanumeric;
use rand::Rng;
use shared_memory::{Shmem, ShmemConf, ShmemError};
use tempfile::NamedTempFile;

pub const SHMEM_SIZE: usize = 1024 * FRAME_SIZE;

#[doc(hidden)]
pub const OBSERVER_IMAGE: &[u8] = include_bytes!(env!("BIOS_PATH"));

#[derive(Clone)]
struct ChildWrapper(Arc<Mutex<Child>>);

impl ChildWrapper {
    pub fn try_wait(&self) -> io::Result<Option<ExitStatus>> {
        self.0.lock().unwrap().try_wait()
    }

    pub fn get_output(&self) -> String {
        let mut output = String::new();
        self.0
            .lock()
            .unwrap()
            .stdout
            .as_mut()
            .unwrap()
            .read_to_string(&mut output)
            .unwrap();

        output
    }

    pub fn id(&self) -> u32 {
        self.0.lock().unwrap().id()
    }

    pub fn kill(&self) -> io::Result<()> {
        self.0.lock().unwrap().kill()
    }
}

pub struct Vm {
    mem: Rc<Shmem>,
    process: ChildWrapper,
    num_queues: usize,
    queue_byte_size: usize,
    page_frames_per_queue: usize,
    observers_created: bool,
}

/// The VM Observer maps a large region of shared memory.
/// This region is referred to in 4KiB frames.
/// The first frame is the control frame.
/// After the control frame follow some number of command frames.
/// Finally, the rest of the shared memory is filled with data frames.
pub struct VmObserver {
    process: ChildWrapper,
    queue: Queue<Host>,
    next_command_frame: u32,
    num_queued: usize,
    page_frames_allocated: usize,
    next_page_frame: u32,
    active_time: Duration,
    page_mapper: PageMapper,
    waiting: usize,
    num_to_discard: usize,
    max_len: usize,

    // Keep a copy of the shared memory so it won't be deallocated while we're using it.
    _shmemcopy: Rc<Shmem>,
}

unsafe impl Send for VmObserver {}
unsafe impl Sync for VmObserver {}

unsafe impl Send for Vm {}
unsafe impl Sync for Vm {}

pub struct PageAllocator<'a> {
    next_page_frame: &'a mut u32,
    page_frames_allocated: &'a mut usize,
    mapper: &'a mut PageMapper,
}

impl<'a> PageAllocator<'a> {
    pub fn fill_and_allocate_page(&mut self, address: u64, data: &[u8], permissions: Permissions) -> MemoryMapping {
        let frame_index = *self.next_page_frame + self.mapper.min_index() as u32;
        *self.next_page_frame = (*self.next_page_frame + 1) % self.mapper.num_page_frames() as u32;
        *self.page_frames_allocated += 1;

        if *self.page_frames_allocated >= self.mapper.num_page_frames() {
            panic!("Ran out of page frames!");
        }

        let page = self.mapper.page_mut(frame_index as usize);
        let offset = (address & 0xfff) as usize;
        page.fill(0xCC);
        page[offset..offset + data.len()].copy_from_slice(data);

        MemoryMapping::new(address & !(0b1111_1111_1111), frame_index, permissions)
    }

    pub fn allocate_page(&mut self, address: u64, data: &[u8], permissions: Permissions) -> MemoryMapping {
        let frame_index = *self.next_page_frame + self.mapper.min_index() as u32;
        *self.next_page_frame = (*self.next_page_frame + 1) % self.mapper.num_page_frames() as u32;
        *self.page_frames_allocated += 1;

        if *self.page_frames_allocated >= self.mapper.num_page_frames() {
            panic!("Ran out of page frames!");
        }

        let page = self.mapper.page_mut(frame_index as usize);
        let offset = (address & 0xfff) as usize;
        page[offset..offset + data.len()].copy_from_slice(data);

        MemoryMapping::new(address & !(0b1111_1111_1111), frame_index, permissions)
    }

    pub fn fill_and_allocate_multi_page<'data>(
        &mut self, base_address: u64, entries: impl Iterator<Item = (u64, &'data [u8])>, permissions: Permissions,
    ) -> MemoryMapping {
        let frame_index = *self.next_page_frame + self.mapper.min_index() as u32;
        *self.next_page_frame = (*self.next_page_frame + 1) % self.mapper.num_page_frames() as u32;
        *self.page_frames_allocated += 1;

        if *self.page_frames_allocated >= self.mapper.num_page_frames() {
            panic!("Ran out of page frames!");
        }

        let page = self.mapper.page_mut(frame_index as usize);
        page.fill(0xCC);
        for (address, data) in entries {
            let offset = (address & 0xfff) as usize;
            if offset + data.len() > page.len() {
                panic!(
                    "Memory mapping out of bounds: mapping {:02X?} at 0x{:X} will cross page bounds",
                    data, address
                );
            }
            page[offset..offset + data.len()].copy_from_slice(data);
        }

        MemoryMapping::new(base_address & !(0b1111_1111_1111), frame_index, permissions)
    }

    pub fn allocate_multi_page<'data>(
        &mut self, base_address: u64, entries: impl Iterator<Item = (u64, &'data [u8])>, permissions: Permissions,
    ) -> MemoryMapping {
        let frame_index = *self.next_page_frame + self.mapper.min_index() as u32;
        *self.next_page_frame = (*self.next_page_frame + 1) % self.mapper.num_page_frames() as u32;
        *self.page_frames_allocated += 1;

        if *self.page_frames_allocated >= self.mapper.num_page_frames() {
            panic!("Ran out of page frames!");
        }

        let page = self.mapper.page_mut(frame_index as usize);
        for (address, data) in entries {
            let offset = (address & 0xfff) as usize;
            if offset + data.len() > page.len() {
                panic!(
                    "Memory mapping out of bounds: mapping {:02X?} at 0x{:X} will cross page bounds",
                    data, address
                );
            }
            page[offset..offset + data.len()].copy_from_slice(data);
        }

        MemoryMapping::new(base_address & !(0b1111_1111_1111), frame_index, permissions)
    }
}

fn random_name(prefix: &str) -> String {
    prefix
        .chars()
        .chain(rand::thread_rng().sample_iter(&Alphanumeric).take(6).map(char::from))
        .collect::<String>()
}

pub struct MemoryMapper<'a> {
    mappings: &'a mut MemoryMappings,
}

impl<'a> MemoryMapper<'a> {
    #[inline(always)]
    pub fn set<I: Iterator<Item = MemoryMapping>>(self, mappings: I) {
        self.mappings.recycle(mappings);

        // Prevent drop() from running
        let _nodrop = ManuallyDrop::new(self);
    }
}

/// This drop implementation ensures memory mappings are always reset;
/// You can set new memory mappings by calling [`MemoryMapper::set`].
/// If you don't call that method, the memory mappings will be reset here.
impl<'a> Drop for MemoryMapper<'a> {
    #[inline]
    fn drop(&mut self) {
        self.mappings.recycle([].into_iter());
    }
}

pub struct DebugRegsWriter<'a>(&'a mut DebugRegs);

impl<'a> DebugRegsWriter<'a> {
    #[inline(always)]
    pub fn set(self, regs: DebugRegs) {
        *self.0 = regs;

        // Prevent drop() from running
        let _nodrop = ManuallyDrop::new(self);
    }
}

impl<'a> Drop for DebugRegsWriter<'a> {
    #[inline]
    fn drop(&mut self) {
        self.0.dr7 = 0;
    }
}

pub struct ExtendedRegsWriter<'a> {
    regs: &'a mut ExtendedRegs,
    offsets: &'a Layout,
    xstate_bv: u64,
}

const XSTATE_X87: u64 = 1 << 0;
const XSTATE_SSE: u64 = 1 << 1;
const XSTATE_XMM: u64 = 1 << 2;

impl<'a> ExtendedRegsWriter<'a> {
    #[inline]
    pub fn set_legacy(&mut self, regs: XsaveLegacyArea) {
        *self.regs.legacy_area_mut() = regs;
        self.xstate_bv |= XSTATE_X87 | XSTATE_SSE;
    }

    #[inline]
    pub fn set_ymm(&mut self, regs: YmmRegs) {
        assert!(self.offsets.avx256.available);
        unsafe {
            *self.regs.component_mut::<YmmRegs>(self.offsets.avx256.offset as usize) = regs;
        };

        self.xstate_bv |= XSTATE_XMM;
    }

    #[inline]
    pub fn avx2_available(&self) -> bool {
        self.offsets.avx256.available
    }
}

impl<'a> Drop for ExtendedRegsWriter<'a> {
    #[inline]
    fn drop(&mut self) {
        let header = self.regs.header_mut();
        header.xcomp_bv = 0;
        header.xstate_bv = self.xstate_bv;
    }
}

pub struct ResultMemoryAccess<'a> {
    mapper: &'a PageMapper,
    active: &'a [MemoryMapping],
}

impl<'a> Index<usize> for ResultMemoryAccess<'a> {
    type Output = [u8];

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        self.mapper.page(self.active[index].frame_index() as usize)
    }
}

impl<'a> ResultMemoryAccess<'a> {
    #[inline]
    pub fn iter(&'a self) -> impl Iterator<Item = &'a [u8]> {
        self.active.iter().map(|m| self.mapper.page(m.frame_index() as usize) as &_)
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.active.len()
    }

    #[must_use]
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

pub struct VmOptions {
    cpuset: Option<CpuSet>,
}

#[derive(Debug, thiserror::Error)]
pub enum StartVmError {
    #[error("unable to create a temporary file: {}", .0)]
    TempFileFailed(std::io::Error),

    #[error("unable to create shared memory: {}", .0)]
    ShMemFailed(ShmemError),

    #[error("unable to start qemu: {}", .0)]
    SpawnQemuFailed(std::io::Error),

    #[error("qemu exited early with status {}: {}", .status, .stdout)]
    QemuEaryExit { status: ExitStatus, stdout: String },
}

impl VmOptions {
    pub fn set_affinity(&mut self, cpuset: CpuSet) {
        self.cpuset = Some(cpuset);
    }

    fn launch_vm_process(&self, bootdisk_file: NamedTempFile, name: String, mem: &Shmem) -> Result<Child, StartVmError> {
        let qemu_path = std::env::var("LIBLISA_QEMU_PATH").unwrap_or(String::from("qemu-system-x86_64"));
        let mut cmd = Command::new(qemu_path);
        let cpu = std::env::var("LIBLISA_QEMU_CPU").unwrap_or(String::from("host"));
        let enable_kvm = {
            let enable_kvm = std::env::var("LIBLISA_QEMU_ENABLE_KVM").unwrap_or(String::from("1"));
            enable_kvm != "0" && enable_kvm != "no" && enable_kvm != "off"
        };
        let nocapture = {
            let nocapture = std::env::var("LIBLISA_NOCAPTURE").unwrap_or(String::from("0"));
            nocapture != "0" && nocapture != "no" && nocapture != "off"
        };
        cmd.args([
            "-drive",
            &format!("format=raw,file={}", bootdisk_file.path().display()),
            "--no-reboot",
            "-m",
            "512M",
            "-device",
            "isa-debug-exit,iobase=0xf4,iosize=0x04",
            "-device",
            "ivshmem-plain,memdev=hostmem",
            "-object",
            &format!(
                "memory-backend-file,size={},share=on,mem-path=/dev/shm/{},id=hostmem",
                SHMEM_SIZE, name
            ),
            "-display",
            "none",
            "-serial",
            "stdio",
        ]);

        if enable_kvm {
            cmd.arg("-enable-kvm");
        }

        cmd.args(["-cpu", &cpu]);

        if !nocapture {
            cmd.stdout(Stdio::piped());
            cmd.stdin(Stdio::piped());
        }

        unsafe {
            let cpuset = self.cpuset;
            cmd.pre_exec(move || {
                if let Some(cpuset) = &cpuset {
                    nix::sched::sched_setaffinity(Pid::from_raw(0), cpuset).unwrap();

                    Ok(())
                } else {
                    Ok(())
                }
            });
        }

        let mut process = cmd.spawn().map_err(StartVmError::SpawnQemuFailed)?;

        let current = unsafe {
            // SAFETY: mem will stay alive beyond this function. The pointer will be dropped at the end of this function.
            make_atomic_u32(mem.as_ptr().wrapping_add(ControlFrame::<Host>::CURRENT_OFFSET) as *mut u32)
        };

        // When the observer is initialised, it resets `current` to 0.
        while current.load(Ordering::Acquire) == u32::MAX {
            if let Some(status) = process.try_wait().unwrap() {
                // Make sure to clean up the shared memory file we created before panicking
                fs::remove_file(format!("/dev/shm/{}", mem.get_os_id())).ok();

                let mut stdout = String::new();
                process.stdout.unwrap().read_to_string(&mut stdout).unwrap();
                return Err(StartVmError::QemuEaryExit {
                    status,
                    stdout,
                })
            }

            std::thread::sleep(Duration::from_millis(25));
        }

        Ok(process)
    }

    pub fn start(self, num: usize) -> Result<Vm, StartVmError> {
        let frames_available = (SHMEM_SIZE / FRAME_SIZE) - num;
        let total_frames_per_queue = frames_available / num;
        let command_frames_per_queue = total_frames_per_queue / 4;
        let page_frames_per_queue = total_frames_per_queue - command_frames_per_queue;

        let bootdisk_file = NamedTempFile::new().map_err(StartVmError::TempFileFailed)?;
        fs::write(bootdisk_file.path(), OBSERVER_IMAGE).map_err(StartVmError::TempFileFailed)?;

        let name = random_name("vx-");
        let mem = ShmemConf::new()
            .size(SHMEM_SIZE)
            .os_id(&name)
            .create()
            .map_err(StartVmError::ShMemFailed)?;

        // Zero all memory
        unsafe {
            std::ptr::write_bytes(mem.as_ptr(), 0, mem.len());
        }

        let queue_byte_size = (1 + command_frames_per_queue) * FRAME_SIZE;
        // Setup the control frames
        for control_frame_index in 0..num {
            unsafe {
                // SAFETY: Nothing else is currently writing to this new shmem, so we can update it freely.
                // SAFETY: ControlFrameData only contains types that are always valid.
                let ptr = mem.as_ptr().add(control_frame_index * queue_byte_size);
                let ptr = ptr as *mut ControlFrameData;
                (*ptr).next.store(0, Ordering::Release);
                (*ptr).current.store(u32::MAX, Ordering::Release);
                std::ptr::write_volatile(&mut (*ptr).num_command_frames, command_frames_per_queue as u32);
                std::ptr::write_volatile(
                    &mut (*ptr).next_control_frame,
                    if control_frame_index == num - 1 {
                        // Last control frame does not have a next control frame
                        0
                    } else {
                        ((control_frame_index + 1) * queue_byte_size) as u32
                    },
                );
            }
        }

        let process = self.launch_vm_process(bootdisk_file, name, &mem)?;

        // From this point on it is safe to use the ControlFrame struct directly.
        Ok(Vm {
            mem: Rc::new(mem),
            num_queues: num,
            queue_byte_size,
            page_frames_per_queue,
            process: ChildWrapper(Arc::new(Mutex::new(process))),
            observers_created: false,
        })
    }
}

impl Vm {
    pub fn options() -> VmOptions {
        VmOptions {
            cpuset: None,
        }
    }

    pub fn start(num: usize) -> Result<Vm, StartVmError> {
        Self::options().start(num)
    }

    pub fn first_observer_only(&mut self) -> VmObserver {
        self.observers().next().unwrap()
    }

    /// Returns all observers that share the queue for this VM.
    pub fn observers(&mut self) -> impl Iterator<Item = VmObserver> + '_ {
        if self.observers_created {
            panic!("You cannot call Vm::observers() more than once");
        }

        self.observers_created = true;

        (0..self.num_queues).map(|index| {
            let page_frame_start = self.queue_byte_size * self.num_queues;
            // SAFETY: We created the shmem in new(), and set it to this exact size
            let queue = unsafe { Queue::new(self.mem.as_ptr().add(index * self.queue_byte_size), self.queue_byte_size) };
            VmObserver {
                max_len: queue.control_frame().num_command_frames() as usize - 1,
                queue,
                process: self.process.clone(),
                next_command_frame: 0,
                num_queued: 0,
                page_frames_allocated: 0,
                next_page_frame: 0,
                num_to_discard: 0,
                page_mapper: PageMapper {
                    page_base: unsafe { self.mem.as_ptr().add(page_frame_start) as *mut _ },
                    min_index: self.page_frames_per_queue * index,
                    num_page_frames: self.page_frames_per_queue,
                },
                active_time: Duration::ZERO,
                waiting: 0,
                _shmemcopy: self.mem.clone(),
            }
        })
    }

    pub fn get_affinity(&self) -> nix::Result<CpuSet> {
        let pid = Pid::from_raw(self.process.id() as i32);
        nix::sched::sched_getaffinity(pid)
    }

    pub fn set_affinity(&self, affinity: &CpuSet) -> nix::Result<()> {
        let pid = Pid::from_raw(self.process.id() as i32);
        nix::sched::sched_setaffinity(pid, affinity)
    }

    pub fn copy_affinity_from_current_thread(&self) -> nix::Result<()> {
        let affinity = nix::sched::sched_getaffinity(Pid::from_raw(0))?;
        self.set_affinity(&affinity)
    }
}

pub struct PageMapper {
    page_base: *mut [u8; 4096],
    min_index: usize,
    num_page_frames: usize,
}

impl PageMapper {
    #[inline]
    pub fn page_mut(&mut self, index: usize) -> &mut [u8; 4096] {
        assert!(index < self.min_index + self.num_page_frames);
        assert!(index >= self.min_index);
        unsafe { &mut *self.page_base.wrapping_add(index) }
    }

    #[inline]
    pub fn page(&self, index: usize) -> &[u8; 4096] {
        assert!(index < self.min_index + self.num_page_frames);
        assert!(index >= self.min_index);
        unsafe { &*self.page_base.wrapping_add(index) }
    }

    #[inline]
    pub fn num_page_frames(&self) -> usize {
        self.num_page_frames
    }

    #[inline]
    pub fn min_index(&self) -> usize {
        self.min_index
    }
}

impl Drop for Vm {
    fn drop(&mut self) {
        // Try to properly clean up the resources we used, if we can.
        self.process.kill().ok();
        fs::remove_file(format!("/dev/shm/{}", self.mem.get_os_id())).ok();
    }
}

impl std::fmt::Debug for VmObserver {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VmObserver")
            .field("process", &self.process.id())
            .field("next_command_frame", &self.next_command_frame)
            .field("num_command_frames", &self.queue.control_frame().num_command_frames())
            .field("num_queued", &self.num_queued)
            .field("page_frames_allocated", &self.page_frames_allocated)
            .field("next_page_frame", &self.next_page_frame)
            .field("active_time", &self.active_time)
            .field("waiting", &self.waiting)
            .finish()
    }
}

impl VmObserver {
    #[inline]
    pub fn reserved_range(&self) -> Range<u64> {
        self.queue.control_frame().reserved_range()
    }

    #[inline]
    pub fn queue_full(&mut self) -> bool {
        self.num_queued >= self.max_len()
            || self.page_frames_allocated >= self.page_mapper.num_page_frames() - MemoryMappings::MAX_LEN
    }

    #[inline]
    pub fn max_len(&self) -> usize {
        self.max_len
    }

    #[inline]
    pub fn queue_empty(&mut self) -> bool {
        self.num_queued == 0 && !self.queue.request_available()
    }

    #[inline]
    pub fn layout(&self) -> Layout {
        self.queue.control_frame().xsave_layout().clone()
    }

    fn enqueue_command_unchecked<R: ObservationRequest>(&mut self, request: &mut R) {
        debug_assert!(!self.queue_full());

        let features = CpuFeatures {
            avx2: self.layout().avx256.available,
        };

        let xsave_layout = self.queue.control_frame().xsave_layout().clone();
        let frame = self.queue.command_frame(self.next_command_frame as usize);
        let extended_regs = &mut frame.extended_regs;

        // Recycle the command for re-use, only overwriting the bytes that need to be overwritten.
        // We can safely recycle the command frames because they are all initialised to their default value at the start, and both client and server will always write valid `CommandFrame`s.
        request.setup(
            features,
            &mut frame.gpregs,
            DebugRegsWriter(&mut frame.debug_regs),
            ExtendedRegsWriter {
                regs: extended_regs,
                offsets: &xsave_layout,
                xstate_bv: 0,
            },
            &mut PageAllocator {
                next_page_frame: &mut self.next_page_frame,
                page_frames_allocated: &mut self.page_frames_allocated,
                mapper: &mut self.page_mapper,
            },
            MemoryMapper {
                mappings: &mut frame.memory_mappings,
            },
        );

        // Initialize all other state to their default values for now
        let extended_regs = &mut frame.extended_regs;
        let header = extended_regs.header();

        // Restore SSE, AVX & x87 (but since xstate_bv = 0, this will initialize them to their default values)
        frame.restore_extended_registers = 0b111;
        // Do not save SSE, AVX & x87 registers unless we explicitly request it
        frame.save_extended_registers = header.xstate_bv;

        let next = (self.next_command_frame + 1) % self.queue.control_frame().num_command_frames();
        self.queue.control_frame().update_next(next);
        // println!("next = {}", next);
        self.next_command_frame = next;
        self.num_queued += 1;
    }

    #[inline(always)]
    fn receive_result_unchecked(&mut self) -> Option<(&CommandFrame, &PageMapper)> {
        debug_assert!(self.num_queued > 0);
        // println!("{:?}", self.queue);
        match self.queue.try_dequeue() {
            Some(o) => {
                self.page_frames_allocated -= o.memory_mappings.len();
                self.num_queued -= 1;
                Some((&*o, &self.page_mapper))
            },
            None => {
                // println!("Waiting: {}", self.waiting);
                self.waiting += 1;
                // add a delay of roughly a few seconds before we do a few expensive checks to make sure the process is still running.
                if self.waiting >= 10_000_000 {
                    self.waiting = 0;
                    if let Some(exit_code) = self.process.try_wait().unwrap() {
                        panic!("VM crashed: {} [{}]", exit_code, self.process.get_output());
                    }
                }

                None
            },
        }
    }

    /// You should avoid using this function, and instead batch your requests. See [`VmObserver::batch`].
    /// This is just a wrapper around that function.
    #[inline]
    pub fn single<R: ObservationRequest<Result = ()>>(&mut self, request: R) {
        self.batch_iter(once(request)).for_each(drop)
    }

    /// For optimal performance, you should batch your observation requests into groups of at least a few dozen.
    /// If you choose groups that are too small (for example, 1 or 10), you may see much slower execution.
    /// In our testing, properly batched requests took around 460ns to complete.
    /// Batching by 10 increases this to 510ns. Batching by 1 increases this to 906ns.
    /// Batches of at least around 250 requests are needed for optimal performance.
    #[inline]
    pub fn batch<R: ObservationRequest, I: IntoIterator<Item = R>>(
        &mut self, requests: I, result_collector: &mut Vec<R::Result>,
    ) {
        for result in self.batch_iter(requests.into_iter()) {
            result_collector.push(result);
        }
    }

    #[inline(always)]
    fn spinwait_step(&self) {
        #[cfg(target_arch = "x86_64")]
        // PAUSE signals to the CPU that we're in a spin-wait loop.
        // This allows the CPU to optimize power usage and do SMT/HyperThreading.
        // PAUSE is recommended up to "a few hundreds of cycles", which is the case for the observations we're making.
        // By not yielding to the OS we avoid the latency that would come with context switching.
        unsafe {
            asm! {
                "pause",
                options(nomem, nostack, preserves_flags),
            };
        }

        if self.num_queued >= self.max_len() / 2 {
            std::thread::sleep(Duration::from_micros(1));
        }

        // As a back-up, if this is somehow not running on x86, we just yield to the OS.
        #[cfg(not(target_arch = "x86_64"))]
        {
            std::thread::yield_now();
        }
    }

    /// For optimal performance, you should batch your observation requests into groups of at least a few dozen.
    /// If you choose groups that are too small (for example, 1 or 10), you may see much slower execution.
    /// In our testing, properly batched requests took around 460ns to complete.
    /// Batching by 10 increases this to 510ns. Batching by 1 increases this to 906ns.
    /// Batches of at least around 250 requests are needed for optimal performance.
    #[inline]
    pub fn batch_iter<'me, R: ObservationRequest + 'me, I: Iterator<Item = R> + 'me>(
        &'me mut self, requests: I,
    ) -> ObserveIter<'me, R, I> {
        // If the queue is filled with entries that we are going to discard,
        // make place for at least one new observation in the queue.
        while self.num_to_discard > 0 {
            while let Some((..)) = self.receive_result_unchecked() {
                self.num_to_discard -= 1;
                if self.num_to_discard == 0 {
                    break
                }
            }

            if !self.queue_full() {
                break
            } else {
                self.spinwait_step();
            }
        }

        ObserveIter {
            observer: self,
            requests: requests.fuse(),
            queue: VecDeque::new(),
        }
    }

    pub fn debug_dump(&self) {
        println!("Active time: {:?}", self.active_time);
    }

    fn discard_pending(&mut self) {
        self.num_to_discard = self.num_queued;
    }
}

#[derive(Copy, Clone, Debug)]
pub struct CpuFeatures {
    avx2: bool,
}

impl CpuFeatures {
    pub fn avx2_available(&self) -> bool {
        self.avx2
    }
}

pub trait ObservationRequest {
    type Result;

    /// `setup` is called when setting up the observation.
    /// You should either call `gpregs` or make sure to overwrite all registers.
    /// You must call `mapper.set(...)`. If you don't, all memory mappings are cleared.
    fn setup(
        &mut self, features: CpuFeatures, gpregs: &mut GpRegs, debug_regs: DebugRegsWriter<'_>,
        extended_regs: ExtendedRegsWriter<'_>, alloc: &mut PageAllocator<'_>, mapper: MemoryMapper<'_>,
    );

    /// `result` is called after the observation has been made.
    /// `gpregs` contains the state of the general-purpose registers after execution.
    /// `memory` is an iterator over the contents of all pages that were mapped.
    fn result(
        self, features: CpuFeatures, gpregs: &GpRegs, debug_regs: &DebugRegs, extended_regs: &ExtendedRegs,
        memory: ResultMemoryAccess<'_>,
    ) -> Self::Result;
}

pub struct ObserveIter<'observer, R, I> {
    observer: &'observer mut VmObserver,
    requests: Fuse<I>,
    queue: VecDeque<R>,
}

impl<R: ObservationRequest, I: Iterator<Item = R>> Iterator for ObserveIter<'_, R, I> {
    type Item = R::Result;

    fn next(&mut self) -> Option<Self::Item> {
        let features = CpuFeatures {
            avx2: self.observer.layout().avx256.available,
        };

        while !self.observer.queue_full() {
            if let Some(mut request) = self.requests.next() {
                // The queue is never full if we are here.
                self.observer.enqueue_command_unchecked(&mut request);
                self.queue.push_back(request);
            } else {
                break;
            }
        }

        if let Some(entry) = self.queue.pop_front() {
            loop {
                // We will always have at least one entry in the queue pending for us here.
                let num_to_discard = self.observer.num_to_discard;
                if let Some((result, page_mapper)) = self.observer.receive_result_unchecked() {
                    if num_to_discard > 0 {
                        self.observer.num_to_discard -= 1;
                        continue;
                    }

                    let memory = ResultMemoryAccess {
                        mapper: page_mapper,
                        active: result.memory_mappings.active(),
                    };

                    return Some(entry.result(features, &result.gpregs, &result.debug_regs, &result.extended_regs, memory));
                } else {
                    self.observer.spinwait_step();
                }
            }
        }

        None
    }
}

impl<R, I> Drop for ObserveIter<'_, R, I> {
    fn drop(&mut self) {
        self.observer.discard_pending()
    }
}
