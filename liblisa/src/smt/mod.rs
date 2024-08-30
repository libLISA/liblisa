//! A generic interface for SMT solvers.
//!
//! We do not want libLISA to depend on a specific SMT solver.
//! This pulls in unwanted C dependencies that make the library less portable.
//!
//! The generic [`SmtSolver`] trait abstracts over the SMT solver implementation.
//! This allows us to specify operations that use an SMT solver,
//! but leave the actual implementation up to a separate crate (`liblisa-z3`) that can be imported when necessary.

mod cache;
mod solver;
mod tree;

#[cfg(feature = "z3")]
pub mod z3;

use std::collections::HashMap;
use std::fs::File;
use std::io::{BufReader, Read, Seek, SeekFrom, Write};
use std::path::Path;

pub use cache::*;
pub use solver::*;

/// A [`SolverCache`] that persists its cache to disk.
pub struct FileCache {
    map: HashMap<AssertionHash, CacheResult>,
    backing: File,
}

impl FileCache {
    /// Loads or creates a new cache at the provided path.
    /// Truncates the file if the end does not contain valid cache data.
    /// This ensures the cache can still be used (partially) if a crash occurs during a write to the cache.
    pub fn new(path: &Path) -> Self {
        let mut map = HashMap::new();
        let mut pos = 0;
        match File::open(path) {
            Ok(mut file) => {
                let size = {
                    let len = file.seek(SeekFrom::End(0)).unwrap();
                    file.seek(SeekFrom::Start(0)).unwrap();
                    len
                };
                let mut r = BufReader::new(file);
                let mut entry = [0u8; 21];
                loop {
                    match r.read_exact(&mut entry) {
                        Ok(_) => {
                            let result = match entry[20] {
                                0 => CacheResult::Unsat,
                                1 => CacheResult::Unknown,
                                2 => CacheResult::Sat,
                                _ => unreachable!(),
                            };

                            map.insert(AssertionHash::from_bytes(entry[..20].try_into().unwrap()), result);
                            pos += 21;
                        },
                        Err(_) => {
                            if pos != size {
                                eprintln!("Truncating {} bytes in solver cache", size - pos);
                                r.into_inner().set_len(pos).unwrap();
                            }

                            break
                        },
                    }
                }
            },
            Err(e) => eprintln!("Unable to open {path:?}: {e}"),
        }

        FileCache {
            map,
            backing: File::options().append(true).create(true).open(path).unwrap(),
        }
    }
}

impl SolverCache for FileCache {
    fn get(&mut self, hash: &AssertionHash) -> Option<CacheResult> {
        self.map.get(hash).cloned()
    }

    fn insert(&mut self, hash: AssertionHash, result: CacheResult) {
        let mut data = [0u8; 21];
        data[..20].copy_from_slice(hash.as_bytes());
        data[20] = match result {
            CacheResult::Unsat => 0,
            CacheResult::Unknown => 1,
            CacheResult::Sat => 2,
        };

        self.map.insert(hash, result);

        self.backing.write_all(&data).unwrap();
    }
}
