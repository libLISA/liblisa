use std::fs;
use std::path::Path;

use nix::sched::CpuSet;
use nix::unistd::Pid;

#[derive(Debug)]
pub struct Cache {
    id: u32,
    level: u32,
    shared_with: CpuSet,
}

#[derive(Debug)]
pub struct CpuCaches {
    caches: Vec<Cache>,
}

#[derive(Debug)]
pub struct CpuTopology {
    core_id: u32,
    // core_cpus: CpuSet,
}

#[derive(Debug)]
pub struct CpuInfo {
    id: u32,
    caches: CpuCaches,
    topology: CpuTopology,
}

impl CpuInfo {
    pub fn all() -> Result<Vec<CpuInfo>, Box<dyn std::error::Error>> {
        let mut result = Vec::new();
        let path = "/sys/devices/system/cpu/";
        for dir in std::fs::read_dir(path)? {
            let entry = dir?;
            if entry.file_type()?.is_dir()
                && entry.file_name().to_str().map(|v| v.starts_with("cpu")).unwrap_or(false)
                && entry
                    .file_name()
                    .to_str()
                    .and_then(|s| s.strip_prefix("cpu").map(|s| s.trim().chars().all(char::is_numeric)))
                    .unwrap_or(false)
            {
                result.push(Self::from_path(entry.path())?);
            }
        }

        Ok(result)
    }

    pub fn from_path<P: AsRef<Path>>(path: P) -> Result<CpuInfo, Box<dyn std::error::Error>> {
        let path = path.as_ref();
        let id = path.file_name().unwrap().to_str().unwrap();
        let id = id.strip_prefix("cpu").unwrap().parse::<u32>()?;

        Ok(CpuInfo {
            id,
            caches: CpuCaches::from_path(path.join("cache"))?,
            topology: CpuTopology::from_path(path.join("topology"))?,
        })
    }

    pub fn id(&self) -> u32 {
        self.id
    }

    pub fn caches(&self) -> &CpuCaches {
        &self.caches
    }

    pub fn topology(&self) -> &CpuTopology {
        &self.topology
    }
}

fn hex_str_to_cpuset(s: &str) -> Result<CpuSet, Box<dyn std::error::Error>> {
    let mut set = CpuSet::new();
    for (index, c) in s.trim().chars().rev().filter(|&c| c != ',').enumerate() {
        let n = u32::from_str_radix(&c.to_string(), 16)?;
        for offset in 0..4 {
            if (n >> offset) & 1 != 0 {
                set.set(index * 4 + offset)?;
            }
        }
    }

    Ok(set)
}

impl CpuCaches {
    pub fn from_path<P: AsRef<Path>>(path: P) -> Result<CpuCaches, Box<dyn std::error::Error>> {
        let mut caches = Vec::new();
        for dir in std::fs::read_dir(&path)? {
            let entry = dir?;
            if entry.file_type()?.is_dir() && entry.file_name().to_str().unwrap().starts_with("index") {
                // TODO: Id might not be available
                let id = fs::read_to_string(entry.path().join("id"))
                    .unwrap_or(String::from("0"))
                    .trim()
                    .parse::<u32>()?;
                let level = fs::read_to_string(entry.path().join("level"))?.trim().parse::<u32>()?;
                let shared_cpu_map = fs::read_to_string(entry.path().join("shared_cpu_map"))?;
                let shared_with = hex_str_to_cpuset(&shared_cpu_map)?;

                caches.push(Cache {
                    id,
                    level,
                    shared_with,
                });
            }
        }

        Ok(CpuCaches {
            caches,
        })
    }

    pub fn caches(&self) -> impl Iterator<Item = &Cache> {
        self.caches.iter()
    }
}

impl Cache {
    pub fn id(&self) -> u32 {
        self.id
    }

    pub fn restrict_current_thread_affinity_to_shared_caches(&self) -> nix::Result<()> {
        nix::sched::sched_setaffinity(Pid::from_raw(0), &self.shared_with)
    }

    pub fn level(&self) -> u32 {
        self.level
    }

    pub fn shared_with(&self) -> CpuSet {
        self.shared_with
    }
}

impl CpuTopology {
    pub fn from_path<P: AsRef<Path>>(path: P) -> Result<CpuTopology, Box<dyn std::error::Error>> {
        let path = path.as_ref();
        let core_id = fs::read_to_string(path.join("core_id"))?.trim().parse()?;
        // let core_cpus = hex_str_to_cpuset(&fs::read_to_string(path.join("core_cpus"))?)?;

        Ok(CpuTopology {
            core_id,
            // core_cpus,
        })
    }

    pub fn core_id(&self) -> u32 {
        self.core_id
    }

    // pub fn core_cpus(&self) -> CpuSet {
    //     self.core_cpus
    // }
}
