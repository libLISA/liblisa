use std::collections::HashMap;
use std::fs::File;
use std::io::{self, BufWriter, Seek, Write};
use std::marker::PhantomData;
use std::os::unix::prelude::FileExt;
use std::path::Path;
use std::sync::Mutex;

use liblisa::arch::Arch;
use liblisa::encoding::dataflows::{Dataflows, MemoryAccesses};
use liblisa::instr::Instruction;
use liblisa_enc::cache::{Cache, CombinedCache, EncodingAnalysisCache, HashMapCache, NoCache};
use liblisa_enc::{AccessAnalysisError, DataflowAnalysisError, JsonThresholdValues};
use log::trace;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

#[derive(Default)]
pub struct IndexMap {
    b1: HashMap<[u8; 1], usize>,
    b2: HashMap<[u8; 2], usize>,
    b3: HashMap<[u8; 3], usize>,
    b4: HashMap<[u8; 4], usize>,
    b5: HashMap<[u8; 5], usize>,
    b6: HashMap<[u8; 6], usize>,
    b7: HashMap<[u8; 7], usize>,
    b8: HashMap<[u8; 8], usize>,
    b9: HashMap<[u8; 9], usize>,
    b10: HashMap<[u8; 10], usize>,
    b11: HashMap<[u8; 11], usize>,
    b12: HashMap<[u8; 12], usize>,
    b13: HashMap<[u8; 13], usize>,
    b14: HashMap<[u8; 14], usize>,
    b15: HashMap<[u8; 15], usize>,
    b16: HashMap<[u8; 16], usize>,
}

impl IndexMap {
    pub fn insert(&mut self, instruction: Instruction, index: usize) {
        match instruction.byte_len() {
            1 => self.b1.insert(instruction.bytes().try_into().unwrap(), index),
            2 => self.b2.insert(instruction.bytes().try_into().unwrap(), index),
            3 => self.b3.insert(instruction.bytes().try_into().unwrap(), index),
            4 => self.b4.insert(instruction.bytes().try_into().unwrap(), index),
            5 => self.b5.insert(instruction.bytes().try_into().unwrap(), index),
            6 => self.b6.insert(instruction.bytes().try_into().unwrap(), index),
            7 => self.b7.insert(instruction.bytes().try_into().unwrap(), index),
            8 => self.b8.insert(instruction.bytes().try_into().unwrap(), index),
            9 => self.b9.insert(instruction.bytes().try_into().unwrap(), index),
            10 => self.b10.insert(instruction.bytes().try_into().unwrap(), index),
            11 => self.b11.insert(instruction.bytes().try_into().unwrap(), index),
            12 => self.b12.insert(instruction.bytes().try_into().unwrap(), index),
            13 => self.b13.insert(instruction.bytes().try_into().unwrap(), index),
            14 => self.b14.insert(instruction.bytes().try_into().unwrap(), index),
            15 => self.b15.insert(instruction.bytes().try_into().unwrap(), index),
            16 => self.b16.insert(instruction.bytes().try_into().unwrap(), index),
            other => panic!("Unsupported instruction length: {other}"),
        };
    }

    pub fn get(&self, instruction: &Instruction) -> Option<&usize> {
        match instruction.byte_len() {
            1 => self.b1.get(&<[u8; 1]>::try_from(instruction.bytes()).unwrap()),
            2 => self.b2.get(&<[u8; 2]>::try_from(instruction.bytes()).unwrap()),
            3 => self.b3.get(&<[u8; 3]>::try_from(instruction.bytes()).unwrap()),
            4 => self.b4.get(&<[u8; 4]>::try_from(instruction.bytes()).unwrap()),
            5 => self.b5.get(&<[u8; 5]>::try_from(instruction.bytes()).unwrap()),
            6 => self.b6.get(&<[u8; 6]>::try_from(instruction.bytes()).unwrap()),
            7 => self.b7.get(&<[u8; 7]>::try_from(instruction.bytes()).unwrap()),
            8 => self.b8.get(&<[u8; 8]>::try_from(instruction.bytes()).unwrap()),
            9 => self.b9.get(&<[u8; 9]>::try_from(instruction.bytes()).unwrap()),
            10 => self.b10.get(&<[u8; 10]>::try_from(instruction.bytes()).unwrap()),
            11 => self.b11.get(&<[u8; 11]>::try_from(instruction.bytes()).unwrap()),
            12 => self.b12.get(&<[u8; 12]>::try_from(instruction.bytes()).unwrap()),
            13 => self.b13.get(&<[u8; 13]>::try_from(instruction.bytes()).unwrap()),
            14 => self.b14.get(&<[u8; 14]>::try_from(instruction.bytes()).unwrap()),
            15 => self.b15.get(&<[u8; 15]>::try_from(instruction.bytes()).unwrap()),
            16 => self.b16.get(&<[u8; 16]>::try_from(instruction.bytes()).unwrap()),
            other => panic!("Unsupported instruction length: {other}"),
        }
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.b1.len()
            + self.b2.len()
            + self.b3.len()
            + self.b4.len()
            + self.b5.len()
            + self.b6.len()
            + self.b7.len()
            + self.b8.len()
            + self.b9.len()
            + self.b10.len()
            + self.b11.len()
            + self.b12.len()
            + self.b13.len()
            + self.b14.len()
            + self.b15.len()
            + self.b16.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

pub trait CacheWriteStream: Write {
    fn set_len(&mut self, len: u64);
}

impl CacheWriteStream for File {
    fn set_len(&mut self, len: u64) {
        File::set_len(self, len).unwrap();
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NewCacheItem<T> {
    pub instruction: Instruction,
    pub data: T,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CacheItem<A: Arch> {
    pub instruction: Instruction,
    pub data: CacheItemData<A>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum CacheItemData<A: Arch> {
    MemoryAccesses(Result<MemoryAccesses<A>, AccessAnalysisError<A>>),
    Dataflows(Result<Dataflows<A, ()>, DataflowAnalysisError<A>>),
    ThresholdValues(JsonThresholdValues<A>),
}

pub struct FileBackedCache {
    file: Option<File>,
    reader: File,
}

impl FileBackedCache {
    pub fn new(path: &Path) -> Result<FileBackedCache, io::Error> {
        let ma = File::options().create(true).read(true).append(true).open(path)?;

        let reader = File::options().read(true).open(path)?;

        Ok(FileBackedCache {
            reader,
            file: Some(ma),
        })
    }

    pub fn as_cache<T: Clone + Serialize + DeserializeOwned, Inner: Cache<T>>(
        &mut self, inner: Inner,
    ) -> FileBackedCacheImpl<'_, T, Inner, File> {
        FileBackedCacheImpl::new(&mut self.reader, self.file.take().unwrap(), inner)
    }
}

impl FileBackedCacheLoader {
    pub fn open(
        memory_accesses: &Path, dataflows: &Path, threshold_values: &Path,
    ) -> Result<FileBackedCacheLoader, std::io::Error> {
        Ok(FileBackedCacheLoader {
            memory_accesses: FileBackedCache::new(memory_accesses)?,
            dataflows: FileBackedCache::new(dataflows)?,
            threshold_values: FileBackedCache::new(threshold_values)?,
        })
    }
}

pub struct FileBackedCacheLoader {
    memory_accesses: FileBackedCache,
    dataflows: FileBackedCache,
    threshold_values: FileBackedCache,
}

impl FileBackedCacheLoader {
    pub fn load<A: Arch>(&mut self) -> impl EncodingAnalysisCache<A> + '_ {
        let memory_accesses = self.memory_accesses.as_cache(HashMapCache::new());
        let dataflows = self.dataflows.as_cache(HashMapCache::new());
        let threshold_values = self.threshold_values.as_cache(NoCache);

        CombinedCache::new(memory_accesses, dataflows, threshold_values)
    }
}

pub struct FileBackedCacheImpl<'a, T: Clone, Inner: Cache<T>, W: Write> {
    reader: Mutex<&'a mut File>,
    index: IndexMap,
    writer: Mutex<BufWriter<W>>,
    inner: Inner,
    _phantom: PhantomData<fn() -> T>,
}

fn read_all_at(f: &mut File, buf: &mut [u8], offset: u64) -> io::Result<bool> {
    let mut num_read = 0;
    while num_read < buf.len() {
        let num = f.read_at(&mut buf[num_read..], offset + num_read as u64)?;
        num_read += num;

        if num == 0 {
            return Ok(false)
        }
    }

    Ok(true)
}

impl<'a, T: Clone + Serialize + DeserializeOwned, Inner: Cache<T>, W: CacheWriteStream> FileBackedCacheImpl<'a, T, Inner, W> {
    fn build_index(reader: &mut File) -> (IndexMap, usize, usize) {
        let mut index = IndexMap::default();
        let mut offset = 0;
        let mut last_ok_offset = 0;

        reader.seek(io::SeekFrom::End(0)).unwrap();
        let file_len = reader.stream_position().unwrap();

        let mut data = [0u8; 20];
        while offset < file_len {
            match read_all_at(reader, &mut data, offset) {
                Ok(true) => (),
                _ => break,
            }

            let byte_len = data[0] as usize;
            let len_offset = 1 + byte_len;
            if len_offset > data.len() {
                break
            }

            let instr_bytes = &data[1..len_offset];

            let len = u32::from_le_bytes(data[len_offset..len_offset + 4].try_into().unwrap()) as usize;

            let base_offset = offset as usize + len_offset + 4;
            if base_offset + len > file_len as usize {
                trace!("offset {offset} is truncated");
                break
            } else {
                trace!("offset {offset} is OK, next is {}", base_offset + len);
            }

            let instruction = Instruction::new(instr_bytes);

            index.insert(instruction, base_offset);

            offset = (base_offset + len) as u64;
            last_ok_offset = offset as usize;
        }

        (index, last_ok_offset, file_len as usize)
    }

    pub fn new(reader: &'a mut File, mut writer: W, inner: Inner) -> Self {
        let (index, last_good_offset, file_len) = Self::build_index(reader);

        if last_good_offset != file_len {
            eprintln!("Truncated data found at end of cache; Truncating to {last_good_offset}.");
            writer.set_len(last_good_offset as u64);
        }

        FileBackedCacheImpl {
            reader: Mutex::new(reader),
            index,
            writer: Mutex::new(BufWriter::new(writer)),
            inner,
            _phantom: PhantomData,
        }
    }

    fn get(&self, instruction: &Instruction) -> Option<T> {
        if let Some(&offset) = self.index.get(instruction) {
            let mut size_data = [0u8; 4];
            read_all_at(&mut self.reader.lock().unwrap(), &mut size_data, offset as u64 - 4).unwrap();

            let size = u32::from_le_bytes(size_data);
            let mut data = vec![0u8; size as usize];
            read_all_at(&mut self.reader.lock().unwrap(), &mut data, offset as u64).unwrap();

            match rmp_serde::from_slice(&data) {
                Ok(obj) => Some(obj),
                Err(err) => {
                    eprintln!("Cache corrupted (ignored): {err}");
                    None
                },
            }
        } else {
            None
        }
    }

    fn save(&self, instruction: &Instruction, obj: &T) {
        let mut f = self.writer.lock().unwrap();
        let data = rmp_serde::to_vec(obj).unwrap();

        let mut header = Vec::new();
        header.push(instruction.byte_len() as u8);
        header.extend(instruction.bytes());
        header.extend(&u32::to_le_bytes(data.len() as u32));

        f.write_all(&header).unwrap();
        f.write_all(&data).unwrap();
    }
}

impl<T: Clone + Serialize + DeserializeOwned, Inner: Cache<T>, W: CacheWriteStream> Cache<T>
    for FileBackedCacheImpl<'_, T, Inner, W>
{
    fn get_or_insert_with(&self, instr: &Instruction, new: impl FnOnce(&Instruction) -> T) -> T {
        if let Some(obj) = self.get(instr) {
            obj
        } else {
            let obj = self.inner.get_or_insert_with(instr, new);
            self.save(instr, &obj);

            obj
        }
    }

    fn num_entries(&self) -> usize {
        self.index.len() + self.inner.num_entries()
    }
}

#[cfg(test)]
mod tests {
    use std::fs::OpenOptions;

    use liblisa::instr::Instruction;
    use liblisa_enc::cache::{Cache, NoCache};
    use serde::{Deserialize, Serialize};
    use tempfile::NamedTempFile;

    use super::FileBackedCache;

    #[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
    pub struct TestData {
        x: u64,
        y: Vec<i16>,
    }

    #[test]
    pub fn cache_save_load() {
        let d1 = TestData {
            x: 42,
            y: vec![1, 2, 3, 99, 98, 97],
        };
        let d2 = TestData {
            x: 7,
            y: vec![1, 2],
        };
        let d3 = TestData {
            x: 7,
            y: (0..1000).collect::<Vec<_>>(),
        };

        let i1 = Instruction::new(&[0xff, 0x30]);
        let i2 = Instruction::new(&[0xff, 0x31, 0x00, 0x00]);
        let i3 = Instruction::new(&[0xd7]);
        let i4 = Instruction::new(&[0xd8]);

        let path = NamedTempFile::new().unwrap();

        // Create a new cache and add some entries
        {
            let mut cache = FileBackedCache::new(path.path()).unwrap();
            let cache = cache.as_cache::<TestData, _>(NoCache);

            cache.get_or_insert_with(&i1, |_| d1.clone());
            cache.get_or_insert_with(&i2, |_| d2.clone());
            cache.get_or_insert_with(&i3, |_| d1.clone());
            cache.get_or_insert_with(&i4, |_| d3.clone());
        }

        // Check if all entries are still there
        {
            let mut cache = FileBackedCache::new(path.path()).unwrap();
            let cache = cache.as_cache::<TestData, _>(NoCache);

            assert_eq!(cache.num_entries(), 4);

            assert_eq!(cache.get_or_insert_with(&i1, |_| panic!()), d1);
            assert_eq!(cache.get_or_insert_with(&i2, |_| panic!()), d2);
            assert_eq!(cache.get_or_insert_with(&i3, |_| panic!()), d1);
            assert_eq!(cache.get_or_insert_with(&i4, |_| panic!()), d3);
        }
    }

    #[test]
    pub fn cache_truncate() {
        let d1 = TestData {
            x: 42,
            y: vec![1, 2, 3, 99, 98, 97],
        };
        let d2 = TestData {
            x: 7,
            y: vec![1, 2],
        };
        let d3 = TestData {
            x: 7,
            y: (0..1000).collect::<Vec<_>>(),
        };

        let i1 = Instruction::new(&[0xff, 0x30]);
        let i2 = Instruction::new(&[0xff, 0x31, 0x00, 0x00]);
        let i3 = Instruction::new(&[0xd7]);
        let i4 = Instruction::new(&[0xd8]);

        let path = NamedTempFile::new().unwrap();

        // Create a new cache and add some entries
        {
            let mut cache = FileBackedCache::new(path.path()).unwrap();
            let cache = cache.as_cache::<TestData, _>(NoCache);

            cache.get_or_insert_with(&i1, |_| d1.clone());
            cache.get_or_insert_with(&i2, |_| d2.clone());
            cache.get_or_insert_with(&i3, |_| d1.clone());
            cache.get_or_insert_with(&i4, |_| d3.clone());
        }

        // Check if all entries are still there
        for num in (0..4).rev() {
            println!("Checking relevant entries up to {num}");
            {
                let len = path.path().metadata().unwrap().len();
                let f = OpenOptions::new().write(true).open(path.path()).unwrap();
                f.set_len(len - 1).unwrap();
            }

            let mut cache = FileBackedCache::new(path.path()).unwrap();
            let cache = cache.as_cache::<TestData, _>(NoCache);

            assert!(cache.num_entries() <= 4);

            if num > 0 {
                assert_eq!(cache.get_or_insert_with(&i1, |_| panic!("expected entry missing")), d1);
            }

            if num > 1 {
                assert_eq!(cache.get_or_insert_with(&i2, |_| panic!("expected entry missing")), d2);
            }

            if num > 2 {
                assert_eq!(cache.get_or_insert_with(&i3, |_| panic!("expected entry missing")), d1);
            }
        }
    }

    #[test]
    pub fn cache_truncate_and_write() {
        let d1 = TestData {
            x: 42,
            y: vec![1, 2, 3, 99, 98, 97],
        };
        let d2 = TestData {
            x: 7,
            y: vec![1, 2],
        };
        let d3 = TestData {
            x: 7,
            y: (0..1000).collect::<Vec<_>>(),
        };

        let i1 = Instruction::new(&[0xff, 0x30]);
        let i2 = Instruction::new(&[0xff, 0x31, 0x00, 0x00]);
        let i3 = Instruction::new(&[0xd7]);
        let i4 = Instruction::new(&[0xd8]);

        let path = NamedTempFile::new().unwrap();

        // Create a new cache and add some entries
        {
            let mut cache = FileBackedCache::new(path.path()).unwrap();
            let cache = cache.as_cache::<TestData, _>(NoCache);

            cache.get_or_insert_with(&i1, |_| d1.clone());
            cache.get_or_insert_with(&i2, |_| d2.clone());
            cache.get_or_insert_with(&i3, |_| d1.clone());
            cache.get_or_insert_with(&i4, |_| d3.clone());
        }

        // Truncate the cache so that the last entry becomes invalid
        {
            let len = path.path().metadata().unwrap().len();
            let f = OpenOptions::new().write(true).open(path.path()).unwrap();
            f.set_len(len - 1).unwrap();
        }

        {
            let mut cache = FileBackedCache::new(path.path()).unwrap();
            let cache = cache.as_cache::<TestData, _>(NoCache);

            assert_eq!(cache.get_or_insert_with(&i1, |_| panic!()), d1);
            assert_eq!(cache.get_or_insert_with(&i2, |_| panic!()), d2);
            assert_eq!(cache.get_or_insert_with(&i3, |_| panic!()), d1);
            assert_eq!(cache.get(&i4), None);
            cache.get_or_insert_with(&i4, |_| d3.clone());
        }

        {
            let mut cache = FileBackedCache::new(path.path()).unwrap();
            let cache = cache.as_cache::<TestData, _>(NoCache);

            assert_eq!(cache.get_or_insert_with(&i1, |_| panic!()), d1);
            assert_eq!(cache.get_or_insert_with(&i2, |_| panic!()), d2);
            assert_eq!(cache.get_or_insert_with(&i3, |_| panic!()), d1);
            assert_eq!(cache.get_or_insert_with(&i4, |_| panic!()), d3);
        }
    }

    // struct VecStreamWriter<'a>(&'a mut Vec<u8>);

    // impl Write for VecStreamWriter<'_> {
    //     fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
    //         self.0.extend(buf);
    //         Ok(buf.len())
    //     }

    //     fn flush(&mut self) -> std::io::Result<()> { Ok(()) }
    // }

    // impl CacheWriteStream for VecStreamWriter<'_> {
    //     fn set_len(&mut self, len: u64) {
    //         self.0.resize(len as usize, 0)
    //     }
    // }

    #[test]
    pub fn cache_fuzz() {
        // let d1 = TestData {
        //     x: 42,
        //     y: vec![ 1, 2, 3, 99, 98, 97 ],
        // };
        // let d2 = TestData {
        //     x: 7,
        //     y: vec![ 1, 2 ],
        // };
        // let d3 = TestData {
        //     x: 7,
        //     y: (0..1000).collect::<Vec<_>>(),
        // };

        // let i1 = Instruction::new(&[ 0xff, 0x30 ]);
        // let i2 = Instruction::new(&[ 0xff, 0x31, 0x00, 0x00 ]);
        // let i3 = Instruction::new(&[ 0xd7 ]);
        // let i4 = Instruction::new(&[ 0xd8 ]);

        // // Create a new cache and add some entries
        // let mut bytes = Vec::new();
        // {
        //     let cache = FileBackedCacheImpl::new(&[], VecStreamWriter(&mut bytes), NoCache);

        //     cache.get_or_insert_with(&i1, |_| d1.clone());
        //     cache.get_or_insert_with(&i2, |_| d2.clone());
        //     cache.get_or_insert_with(&i3, |_| d1.clone());
        //     cache.get_or_insert_with(&i4, |_| d3.clone());
        // }

        // // Make sure it never crashes
        // let mut rng = rand::thread_rng();
        // for _ in 0..100_000 {
        //     let mut data = Vec::<u8>::new();
        //     data.extend(&bytes[..rng.gen_range(0..bytes.len())]);

        //     let mut extra = vec![0; rng.gen_range(0..128)];
        //     rng.fill_bytes(&mut extra);
        //     data.extend(extra);

        //     let mut v = Vec::new();
        //     let _ = FileBackedCacheImpl::<TestData, _, _>::new(&data, VecStreamWriter(&mut v), NoCache);
        // }
    }
}
