use native;
use std::os::raw::c_uint;
use std::path::{Path, PathBuf};
use std::fmt;
use std::mem;
use widestring::WideCString;

pub(crate) fn unpack_unp_size(unp_size: c_uint, unp_size_high: c_uint) -> usize {
    (unp_size_high << mem::size_of::<c_uint>() | unp_size) as usize
}

bitflags! {
    pub struct EntryFlags: u32 {
        const SPLIT_BEFORE = 0x1;
        const SPLIT_AFTER = 0x2;
        const ENCRYPTED = 0x4;
        // const RESERVED = 0x8;
        const SOLID = 0x10;
        const DIRECTORY = 0x20;
    }
}

#[derive(Debug)]
pub struct Entry {
    filename: PathBuf,
    flags: EntryFlags,
    unpacked_size: usize,
    file_crc: u32,
    file_time: u32,
    method: u32,
    file_attr: u32,
    dict_size: usize,
    pub(crate) next_volume: Option<PathBuf>,
    pub(crate) bytes: Option<Vec<u8>>,
}

impl Entry {
    #[inline]
    pub fn bytes(&self) -> Option<&Vec<u8>> {
        self.bytes.as_ref()
    }

    #[inline]
    pub fn take_bytes(mut self) -> Option<Vec<u8>> {
        self.bytes.take()
    }

    #[inline]
    pub fn next_volume(&self) -> Option<&PathBuf> {
        self.next_volume.as_ref()
    }
}

impl fmt::Display for Entry {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.filename)?;
        if self.is_directory() {
            write!(f, "/")?
        }
        if self.is_split() {
            write!(f, " (partial)")?
        }
        Ok(())
    }
}

impl From<native::HeaderDataEx> for Entry {
    fn from(header: native::HeaderDataEx) -> Self {
        let filename = unsafe { WideCString::from_ptr_with_nul(header.filename_w.as_ptr()
                                                               as *const _, 1024) }.unwrap();

        Entry {
            filename: PathBuf::from(filename.to_os_string()),
            flags: EntryFlags::from_bits(header.flags).unwrap(),
            unpacked_size: unpack_unp_size(header.unp_size, header.unp_size_high),
            file_crc: header.file_crc,
            file_time: header.file_time,
            method: header.method - 0x30,
            file_attr: header.file_attr,
            dict_size: header.dict_size as usize,
            next_volume: None,
            bytes: None,
        }
    }
}


// Helper trait for implementing Header trait with less duplication.
pub trait ArchiveEntry {
    fn entry(&self) -> &Entry;
}

impl ArchiveEntry for Entry {
    #[inline]
    fn entry(&self) -> &Entry {
        self
    }
}

impl ArchiveEntry for &Entry {
    #[inline]
    fn entry(&self) -> &Entry {
        self
    }
}


pub trait Header {
    fn is_split(&self) -> bool;
    fn is_directory(&self) -> bool;
    fn is_encrypted(&self) -> bool;
    fn is_file(&self) -> bool;

    fn filename(&self) -> &Path;
    fn flags(&self) -> EntryFlags;
    fn unpacked_size(&self) -> usize;
    fn file_crc(&self) -> u32;
    fn file_time(&self) -> u32;
    fn method(&self) -> u32;
    fn file_attr(&self) -> u32;
    fn dict_size(&self) -> usize;
}

impl<T: ArchiveEntry> Header for T {
    #[inline]
    fn is_split(&self) -> bool {
        self.entry().flags.contains(EntryFlags::SPLIT_BEFORE) || self.entry().flags.contains(EntryFlags::SPLIT_AFTER)
    }

    #[inline]
    fn is_directory(&self) -> bool {
        self.entry().flags.contains(EntryFlags::DIRECTORY)
    }

    #[inline]
    fn is_encrypted(&self) -> bool {
        self.entry().flags.contains(EntryFlags::ENCRYPTED)
    }

    #[inline]
    fn is_file(&self) -> bool {
        !self.entry().is_directory()
    }

    #[inline]
    fn filename(&self) -> &Path {
        self.entry().filename.as_path()
    }

    #[inline]
    fn flags(&self) -> EntryFlags {
        self.entry().flags
    }

    #[inline]
    fn unpacked_size(&self) -> usize {
        self.entry().unpacked_size
    }

    /// Unpacked file CRC.
    /// For split files, only the last part contains correct CRC and is only
    /// accessible in list split mode.
    #[inline]
    fn file_crc(&self) -> u32 {
        self.entry().file_crc
    }

    /// File date time in MS-DOS format.
    #[inline]
    fn file_time(&self) -> u32 {
        self.entry().file_time
    }

    /// Packing method, range from weakest to best [0-5].
    #[inline]
    fn method(&self) -> u32 {
        self.entry().method
    }

    #[inline]
    fn file_attr(&self) -> u32 {
        self.entry().file_attr
    }

    /// The dictionary size used.
    #[inline]
    fn dict_size(&self) -> usize {
        self.entry().dict_size
    }
}
