use std::ptr::NonNull;
use std::path::{Path, PathBuf};
use widestring::WideCString;
use std::ptr;

use native;
use crate::entry::*;
use crate::error::*;
use crate::archive::{SharedData, OpenArchive, Operation};

pub struct OpenArchiveReader {
    inner: OpenArchive,
    current_header: Option<Entry>,
    damaged: bool,
}

impl OpenArchiveReader {
    pub fn new(archive: OpenArchive) -> Self {
        Self {
            inner: archive,
            current_header: None,
            damaged: false,
        }
    }

    /// Attempts to read the header of the next file in the archive.
    ///
    /// Returns `None` when end of the archive is reached.
    pub fn read_next_header(&mut self) -> Option<UnrarResult<EntryHeader>> {
        // The damaged flag was set, don't attempt to read any further, stop
        if self.damaged {
            self.current_header = None;
            return None;
        }

        // Skip if unprocessed.
        // TODO: Could do this in EntryHeader drop().
        //       Requires means of passing error message back (could/should use Shared),
        //       which requires refactoring UnrarError.
        let mut unproc = self.current_header.take();
        if unproc.is_some() {
            let result = EntryHeader::new(&mut unproc,
                                          self.inner.handle,
                                          self.inner.shared.clone()).skip();
            if let Err(e) = result {
                self.damaged = true;
                self.inner.shared.volume.borrow_mut().take();
                self.inner.shared.bytes.borrow_mut().take();
                return Some(Err(UnrarError::from(e.code, e.when)));
            }
        }

        let mut header = native::HeaderDataEx::default();
        let read_result = Code::from(unsafe { native::RARReadHeaderEx(self.inner.handle.as_ptr(),
                                                                      &mut header as *mut _)
                                              as u32 }).unwrap();

        self.current_header = Some(match read_result {
            Code::Success => {
                 Entry::from(header)
            },
            Code::EndArchive => {
                self.damaged = true;
                return None;
            },
            _ => {
                self.damaged = true;
                return Some(Err(UnrarError::from(read_result, When::Read)))
            }
        });

        Some(Ok(EntryHeader::new(&mut self.current_header,
                                 self.inner.handle,
                                 self.inner.shared.clone())))
    }
}

/// Wrapper providing the necessary facilities to process the archive entry.
///
/// Works by keeping a reference to the unprocessed `Entry` held by `OpenArchive`.
/// Upon processing, the wrapper gets consumed, yielding the inner Entry.
pub struct EntryHeader<'a> {
    // Borrowing Entry mutably keeps us tied to OpenArchive and ensures that only one
    // unprocessed entry exists at a time. While letting OpenArchive automatically skip entries that
    // were not processed by the user.
    //
    // This also means `unwrap()` is safe, because `entry` can be assumed to be `Some` for the
    // entire lifetime of `EntryHeader`.
    // As long as the implementation makes sure `EntryHeader` gets expired whenever `Entry`
    // gets taken out of the `Option`.
    entry: &'a mut Option<Entry>,
    handle: NonNull<native::HANDLE>,
    shared: SharedData,
}

// NOTE: All functions yielding the inner Entry by value (e.g. by `take()`) _must_ consume self.
impl<'a> EntryHeader<'a> {
    /// `entry` _must_ be Some.
    fn new(entry: &'a mut Option<Entry>,
           handle: NonNull<native::HANDLE>,
           shared: SharedData)
           -> Self
    {
        assert!(entry.is_some(), "BUG: EntryHeader constructed with entry as None");
        Self {
            entry,
            handle,
            shared,
        }
    }

    #[inline]
    fn process(&self, operation: Operation, destination: Option<&WideCString>) -> UnrarResult<()> {
        let process_result = Code::from(unsafe {
            native::RARProcessFileW(
                self.handle.as_ptr(),
                operation as i32,
                destination.map(|x| x.as_ptr() as *const _)
                    .unwrap_or(ptr::null()),
                ptr::null()
            ) as u32
        }).unwrap();

        match process_result {
            Code::Success | Code::EOpen => {
                // EOpen on Process: Next volume not found
                if process_result == Code::EOpen {
                    Err(UnrarError::from(process_result, When::Process))
                } else {
                    Ok(())
                }
            }
            _ => {
                Err(UnrarError::from(process_result, When::Process))
            }
        }
    }

    // Only valid after process().
    #[inline]
    fn next_volume(&self) -> Option<PathBuf> {
        self.shared.volume.borrow_mut()
            .take().map(|x| PathBuf::from(x.to_os_string()))
    }

    #[inline]
    fn process_entry(self, op: Operation, destination: Option<&WideCString>) -> UnrarResult<Entry> {
        let default_destination = self.shared.destination.borrow();
        let dest =
            if op == Operation::Extract {
                destination.or_else(|| default_destination.as_ref())
            } else { None };

        let result = self.process(op, dest);

        self.entry.as_mut().unwrap().next_volume = self.next_volume();
        let entry = self.entry.take().unwrap();
        match result {
            Ok(_) => Ok(entry),
            Err(e) => Err(UnrarError::new(e.code, e.when, entry))
        }
    }

    // TODO: Should this return Entry or Vec<u8>?
    pub fn read_bytes(self) -> UnrarResult<Entry> {
        // Try to reserve the full unpacked size ahead of time.
        // Since apparently we can only read max dictionary size at a time
        // with the callback.
        // TODO: Optionally, stream bytes in dictionary sized chunks.
        //
        // Max dictionary size is 4MB for RAR 3.x and 4.x,
        // and 256MB (32bit) or 1GB (64bit) for RAR 5.0.
        self.shared.bytes.borrow_mut()
            .replace(Vec::with_capacity(self.entry.as_ref().unwrap().unpacked_size()));

        let result = self.process(Operation::Test, None);

        self.entry.as_mut().unwrap().next_volume = self.next_volume();
        self.entry.as_mut().unwrap().bytes = match self.shared.bytes.borrow_mut().take() {
            Some(bytes) => Some(bytes),
            None => return Err(UnrarError::new(Code::Success, When::Process, self.entry.take().unwrap()))
        };

        let entry = self.entry.take().unwrap();
        match result {
            Ok(_) => Ok(entry),
            Err(e) => Err(UnrarError::new(e.code, e.when, entry))
        }
    }

    #[inline]
    pub fn test(self) -> UnrarResult<Entry> {
        self.process_entry(Operation::Test, None)
    }

    #[inline]
    pub fn extract_to<P: AsRef<Path>>(self, destination: P) -> UnrarResult<Entry> {
        let dest = Some(WideCString::from_os_str(destination.as_ref())?);
        self.process_entry(Operation::Extract, dest.as_ref())
    }

    #[inline]
    pub fn extract(self) -> UnrarResult<Entry> {
        self.process_entry(Operation::Extract, None)
    }

    #[inline]
    pub fn skip(self) -> UnrarResult<Entry> {
        self.process_entry(Operation::Skip, None)
    }
}

impl<'a> ArchiveEntry for EntryHeader<'a> {
    #[inline]
    fn entry(&self) -> &Entry {
        &self.entry.as_ref().unwrap()
    }
}
impl<'a> ArchiveEntry for &EntryHeader<'a> {
    #[inline]
    fn entry(&self) -> &Entry {
        &self.entry.as_ref().unwrap()
    }
}
