use std::ptr::NonNull;
use std::path::{Path, PathBuf};
use widestring::WideCString;
use std::ptr;
use std::panic;

use native;
use crate::entry::*;
use crate::error::*;
use crate::archive::{SharedData, OpenArchive, Operation, CallbackControl, UnsafeBytesClosurePointer};

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
                self.inner.shared.volume.take();
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
                debug_assert!(self.inner.shared.bytes_closure_panic.take().is_none());
                if let Some(err) = self.inner.shared.callback_panic.take() {
                    panic!("{:?}[{:?}]: {:?}", When::Read, read_result, err);
                } else if let Some(err) = self.inner.shared.callback_error.take() {
                    // FIXME: Could handle gracefully by returning the error.
                    //return Some(Err(Error::from_callback(err, When::Read)))
                    panic!("{:?}[{:?}]: {:?}", When::Read, read_result, err);
                }

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
                if let Some(err) = self.shared.bytes_closure_panic.take() {
                    // This should only occur after RARProcessFile(W) and with Code::Unknown.
                    debug_assert_eq!(process_result, Code::Unknown,
                                     "User closure panicked with an unusual process result");
                    panic::resume_unwind(err);
                } else if let Some(err) = self.shared.callback_panic.take() {
                    panic!("{:?}[{:?}]: {:?}", When::Process, process_result, err);
                } else if let Some(err) = self.shared.callback_error.take() {
                    // FIXME: Could handle gracefully by returning the error.
                    //return Some(Err(Error::from_callback(err, When::Process)))
                    panic!("{:?}[{:?}]: {:?}", When::Process, process_result, err);
                }

                Err(UnrarError::from(process_result, When::Process))
            }
        }
    }

    // Only valid _once_ after process().
    #[inline]
    fn next_volume(&self) -> Option<PathBuf> {
        self.shared.volume.take().map(|x| PathBuf::from(x.to_os_string()))
    }

    #[inline]
    fn process_entry(self, op: Operation, destination: Option<&WideCString>) -> UnrarResult<Entry> {
        let default_destination = self.shared.destination.as_ref();
        let dest =
            if op == Operation::Extract {
                destination.or_else(|| default_destination)
            } else { None };

        let result = self.process(op, dest);

        let mut entry = self.entry.take().unwrap();
        entry.next_volume = self.next_volume();
        match result {
            Ok(_) => Ok(entry),
            Err(e) => Err(UnrarError::new(e.code, e.when, entry))
        }
    }

    /// Collect entry bytes using a closure.
    /// The amount of bytes read per call depends on the archive dictionary size.
    ///
    /// Max dictionary size is expected to be 4MB for RAR 3 and 4,
    /// and 256MB (for 32bit) or 1GB (for 64bit) for RAR 5.0.
    ///
    /// # Safety
    /// Closure is assumed to be `UnwindSafe` using `AssertUnwindSafe`. Practically this means that
    /// any changes to external state made in the closure will be retained, when a panic is caught.
    pub fn read_bytes_with<'b>(self, f: impl FnMut(&[u8]) -> CallbackControl + 'b) -> UnrarResult<Entry> {
        // This ought to be safe as long as we ensure that the closure pointer gets dropped
        // somewhere during this function.
        //
        // The closure is boxed and cast into thin pointer, letting us bypass any lifetime
        // restrictions when storing the function in `shared.bytes_closure`.
        self.shared.bytes_closure.borrow_mut().replace(UnsafeBytesClosurePointer::new(f));

        let result = self.process(Operation::Test, None);

        // Important: Ensures the (unsafe) function pointer gets dropped.
        self.shared.bytes_closure.borrow_mut().take();

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
        //
        // Max dictionary size is 4MB for RAR 3.x and 4.x,
        // and 256MB (32bit) or 1GB (64bit) for RAR 5.0.
        self.shared.bytes.borrow_mut()
            .replace(Vec::with_capacity(self.entry.as_ref().unwrap().unpacked_size()));

        let result = self.process(Operation::Test, None);

        let mut entry = self.entry.take().unwrap();
        entry.next_volume = self.next_volume();
        entry.bytes = match self.shared.bytes.borrow_mut().take() {
            Some(bytes) => Some(bytes),
            None => return Err(UnrarError::new(Code::Success, When::Process, self.entry.take().unwrap()))
        };

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
