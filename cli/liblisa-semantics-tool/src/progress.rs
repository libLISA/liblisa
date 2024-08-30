use std::fmt::{Debug, Display};
use std::io::Write;
use std::ops::Deref;
use std::sync::atomic::{AtomicBool, AtomicU32, AtomicUsize, Ordering};
use std::time::Duration;

pub use crate::progress_data;

#[macro_export]
macro_rules! progress_data {
    ($name:ident $(<$( $lt:lifetime ),+>)? { $($field:ident: $ty:ty = $e:expr),* $(,)* }, $display:expr) => {
        {
            struct $name $(<$($lt),+>)? {
                $($field: $ty),*
            }

            impl $(<$($lt),+>)? std::fmt::Display for $name $(<$($lt),+>)? {
                fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    fn force_type(f: impl FnOnce(&mut std::fmt::Formatter<'_>, &$name) -> std::fmt::Result)
                        -> impl FnOnce(&mut std::fmt::Formatter<'_>, &$name) -> std::fmt::Result { f }
                    let display = force_type($display);

                    display(f, self)
                }
            }

            #[allow(clippy::redundant_field_names)]
            $name {
                $($field: $e.into()),*
            }
        }
    }
}

pub struct ProgressUsize(AtomicUsize);

impl Display for ProgressUsize {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let val = self.0.load(Ordering::Relaxed);
        Display::fmt(&val, f)
    }
}

impl Debug for ProgressUsize {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let val = self.0.load(Ordering::Relaxed);
        Debug::fmt(&val, f)
    }
}

impl From<usize> for ProgressUsize {
    fn from(value: usize) -> Self {
        Self::new(value)
    }
}

impl ProgressUsize {
    pub fn new(val: usize) -> Self {
        Self(AtomicUsize::new(val))
    }

    pub fn increment(&self) {
        self.0.fetch_add(1, Ordering::Relaxed);
    }

    pub fn delayed_increment(&self) -> DelayedIncrement<'_> {
        DelayedIncrement(self)
    }
}

pub struct DelayedIncrement<'a>(&'a ProgressUsize);

impl Drop for DelayedIncrement<'_> {
    fn drop(&mut self) {
        self.0.increment();
    }
}

pub struct Progress<T> {
    current: T,
    modified: AtomicU32,
}

impl<T> Deref for Progress<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.modified.fetch_add(1, Ordering::Relaxed);
        &self.current
    }
}

struct SetFalseIfDropped<'a>(&'a AtomicBool);

impl Drop for SetFalseIfDropped<'_> {
    fn drop(&mut self) {
        self.0.store(false, Ordering::Relaxed);
    }
}

impl<T: Sync + Display> Progress<T> {
    pub fn run<K>(init: T, f: impl FnOnce(&Progress<T>) -> K) -> K {
        let running = AtomicBool::new(true);
        let progress = Progress {
            current: init,
            modified: AtomicU32::new(0),
        };
        let progress = &progress;

        let result = std::thread::scope(|scope: &std::thread::Scope<'_, '_>| {
            scope.spawn(|| {
                let mut last_printed_tick = 0;
                while running.load(Ordering::Relaxed) {
                    let tick = progress.modified.load(Ordering::Relaxed);
                    if tick != last_printed_tick {
                        last_printed_tick = tick;
                        eprint!("\r{}", progress.current);
                        std::io::stderr().flush().unwrap();
                    }

                    std::thread::sleep(Duration::from_millis(15));
                }
            });

            let run = || {
                // We need to use a struct here that sets running to false when it is dropped at the end of this scope.
                // f might panic, so we can't be sure that any code we execute after f terminates is ever executed.
                // Panicking will still try to drop the struct, guaranteeing that the progress printing thread in our scope actually terminates.
                let _guard = SetFalseIfDropped(&running);
                f(progress)
            };

            run()
        });

        eprintln!("\r{}", progress.current);

        result
    }
}
