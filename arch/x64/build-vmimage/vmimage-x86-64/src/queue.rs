use liblisa_x64_observer_shmqueue::frame::FRAME_SIZE;
use liblisa_x64_observer_shmqueue::frame::{control::Client, command::CommandFrame};
use liblisa_x64_observer_shmqueue::queue::Queue;

use crate::serial_println;

pub struct Incoming<'a> {
    queues: &'a mut [Queue<Client>],
    current_queue: usize,
}

pub struct PageOffsetTranslator {
    base_offset: usize,
}

impl PageOffsetTranslator {
    pub fn page_offset(&self, index: usize) -> usize {
        self.base_offset + index * FRAME_SIZE
    }
}

impl<'a> Incoming<'a> {
    pub fn new(queues: &'a mut [Queue<Client>]) -> Result<Incoming<'a>, ()> {
        for queue in queues.iter() {
            if queue.control_frame().num_command_frames() == 0 {
                serial_println!("Shared memory has not been set up correctly. `num_command_frames` cannot be 0.");
                return Err(());
            }

            if queue.total_size() < (queue.control_frame().num_command_frames() as usize + 1) * 4096 {
                panic!("Shared memory has not been set up correctly. Not enough memory is available for all queue frames.");
            }
        }

        Ok(Incoming {
            queues,
            current_queue: 0,
        })
    }

    pub fn offset_translator(&self) -> PageOffsetTranslator {
        let frame_offset = self.queues.iter()
            .map(|queue| 1 + queue.control_frame().num_command_frames())
            .sum::<u32>();
        PageOffsetTranslator {
            base_offset: frame_offset as usize * FRAME_SIZE,
        }
    }

    pub fn receive_request(&mut self) -> Option<&mut CommandFrame> {
        let num_queues = self.queues.len();

        for shift in 0..num_queues {
            let index = (self.current_queue + shift) % num_queues;
            if self.queues[index].request_available() {
                self.current_queue = index;
                return self.queues[index].try_dequeue();
            }
        }

        None
    }

    pub fn mark_processed(&mut self) {
        let queue = &mut self.queues[self.current_queue];
        queue.control_frame().update_current(queue.read_index());
        self.current_queue = (self.current_queue + 1) % self.queues.len();
    }
}