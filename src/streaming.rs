pub use streaming_iterator::StreamingIterator;
use std::fmt;
use std::cell::{Cell, UnsafeCell};
use std::marker::PhantomData;
use std::ptr::NonNull;
use std::path::PathBuf;

use native;
use crate::entry::*;
use crate::error::*;
use crate::archive::{RAROperation, SharedData, OpenArchive, Operation};

pub struct OpenArchiveStreamingIter<'a> {
    inner: OpenArchive,
    unprocessed_entry: Option<UnrarResult<UnprocessedEntry<'a>>>,
    damaged: bool,
}

impl<'a> OpenArchiveStreamingIter<'a> {
    pub fn new(archive: OpenArchive) -> Self {
        Self {
            inner: archive,
            unprocessed_entry: None,
            damaged: false,
        }
    }
}

// TODO: Find a way to make Item = UnrarResult<&mut UnprocessedEntry<'a>>
impl<'a> StreamingIterator for OpenArchiveStreamingIter<'a> {
    type Item = UnrarResult<UnprocessedEntry<'a>>;

    // Would be great if this was &mut.
    #[inline]
    fn get(&self) -> Option<&Self::Item> {
        self.unprocessed_entry.as_ref()
    }

    #[inline]
    fn advance(&mut self)  {
        // The damaged flag was set, don't attempt to read any further, stop
        if self.damaged {
            self.unprocessed_entry = None;
            return;
        }

        // Skip unprocessed.
        if let Some(Ok(unproc)) = self.unprocessed_entry.take() {
            if !unproc.is_processed.get() {
                let result = unproc.skip();
                if let Err(e) = result {
                    self.damaged = true;
                    self.inner.user_data.volume.borrow_mut().take();
                    self.inner.user_data.bytes.borrow_mut().take();
                    self.unprocessed_entry = Some(Err(UnrarError::from(e.code, e.when)));
                }
            }
        }

        let mut header = native::HeaderDataEx::default();
        let read_result = Code::from(unsafe { native::RARReadHeaderEx(self.inner.handle.as_ptr(),
                                                                      &mut header as *mut _)
                                              as u32 }).unwrap();

        self.unprocessed_entry = match read_result {
            Code::Success => {
                 Some(Ok(UnprocessedEntry::new(Entry::from(header),
                                               self.inner.handle,
                                               self.inner.user_data.clone())))
            },
            Code::EndArchive => {
                self.damaged = true;
                None
            },
            _ => {
                self.damaged = true;
                Some(Err(UnrarError::from(read_result, When::Read)))
            }
        }
    }
}

/// Represents an unprocessed entry returned by the StreamingIterator
/// implementation, containing the header data in an `Entry` struct.
///
/// Can be processed using the methods `skip`, `test`, `extract` and
/// `read_bytes`. If left unprocessed the iterator will  automatically call
/// `skip`.
///
/// # Panics
///
/// Panics if internal entry accessed after processing.
///
// Lifetime _must_ be tied to a OpenArchive instance.
#[derive(Debug)]
pub struct UnprocessedEntry<'a> {
    // UnsafeCell used so that we can remove inner Entry without &mut.
    // StreamingIterator should prevent multiple instances of UnprocessedEntries
    // from existing, because each item borrows the iterator mutably.
    entry: UnsafeCell<Option<Entry>>,
    handle: NonNull<native::HANDLE>,
    user_data: SharedData,
    // Remember that we're actually mutably borrowing OpenArchive here.
    marker: PhantomData<&'a mut OpenArchive>,
    is_processed: Cell<bool>,
}

impl<'a> UnprocessedEntry<'a> {
    fn new(entry: Entry,
           handle: NonNull<native::HANDLE>,
           user_data: SharedData,)
           -> Self
    {
        Self {
            entry: UnsafeCell::new(Some(entry)),
            is_processed: Cell::new(false),
            handle,
            user_data,
            marker: PhantomData,
        }
    }

    #[inline]
    fn process(&self, op: Operation) -> UnrarResult<()> {
        // Make sure to mark current entry processed.
        self.is_processed.set(true);

        let destination =
            if op == Operation::Extract {
                self.user_data.destination.as_ref()
            } else { None };

        let process_result = Code::from(unsafe {
            native::RARProcessFileW(
                self.handle.as_ptr(),
                RAROperation::from(op) as i32,
                destination.map(|x| x.as_ptr() as *const _)
                    .unwrap_or(0 as *const _),
                0 as *const _
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
        self.user_data.volume.borrow_mut()
            .take().map(|x| PathBuf::from(x.to_os_string()))
    }

    #[inline]
    fn process_entry(&self, op: Operation) -> UnrarResult<Entry> {
        let entry = unsafe { &mut *self.entry.get() };
        assert!(entry.is_some(), "Attempted to process already processed entry");

        let result = self.process(op);

        let mut entry = entry.take().unwrap();
        entry.next_volume = self.next_volume();
        match result {
            Ok(_) => Ok(entry),
            Err(e) => Err(UnrarError::new(e.code, e.when, entry))
        }
    }

    // TODO: Should this return Entry or Vec<u8>?
    pub fn read_bytes(&self) -> UnrarResult<Entry> {
        let entry = unsafe { &mut *self.entry.get() };
        assert!(entry.is_some(), "Attempted to process already processed entry");

        // Try to reserve the full unpacked size ahead of time.
        // Since apparently we can only read max dictionary size at a time
        // with the callback.
        //
        // Max dictionary size is 4MB for RAR 3.x and 4.x,
        // and 256MB (32bit) or 1GB (64bit) for RAR 5.0.
        self.user_data.bytes.borrow_mut()
            .replace(Vec::with_capacity(entry.as_ref().unwrap().unpacked_size()));

        let result = self.process(Operation::Test);

        let mut entry = entry.take().unwrap();
        entry.next_volume = self.next_volume();
        entry.bytes = match self.user_data.bytes.borrow_mut().take() {
            Some(bytes) => Some(bytes),
            None => return Err(UnrarError::new(Code::Success, When::Process, entry))
        };

        match result {
            Ok(_) => Ok(entry),
            Err(e) => Err(UnrarError::new(e.code, e.when, entry))
        }
    }

    // TODO: Should these return Entry or ()?
    #[inline]
    pub fn test(&self) -> UnrarResult<Entry> {
        self.process_entry(Operation::Test)
    }

    #[inline]
    pub fn extract(&self) -> UnrarResult<Entry> {
        self.process_entry(Operation::Extract)
    }

    #[inline]
    pub fn skip(&self) -> UnrarResult<Entry> {
        self.process_entry(Operation::Skip)
    }
}

impl<'a> fmt::Display for UnprocessedEntry<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match unsafe { &mut *self.entry.get() } {
            Some(e) => e.fmt(f),
            None => write!(f, "(processed)"),
        }
    }
}

impl<'a> ArchiveEntry for &UnprocessedEntry<'a> {
    /// Panics if already processed.
    #[inline]
    fn entry(&self) -> &Entry {
        let entry = unsafe { &mut *self.entry.get() }.as_ref();
        assert!(entry.is_some(),
                "Trying to access unprocessed entry that has already been processed");
        entry.unwrap()
    }
}
