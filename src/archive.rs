use native;
use widestring::WideCString;
use regex::Regex;
use std::os::raw::c_int;
use std::fmt;
use std::str;
use std::isize;
use std::slice;
use std::mem;
use std::ptr;
use std::panic;
use std::process;
use std::any;
use std::borrow::Cow;
use std::path::{Path, PathBuf};
use std::ffi::CStr;
use std::iter::repeat;
use std::ptr::NonNull;
use std::boxed::Box;
use std::rc::Rc;
use std::cell::{Cell, RefCell};
use std::ops::Deref;
use std::convert::TryInto;

use crate::error::*;
use crate::entry::*;
use crate::streaming::*;
use crate::reader::*;

// TODO: Move to unrar_sys?
#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpenMode {
    List = native::RAR_OM_LIST,
    Extract = native::RAR_OM_EXTRACT,
    ListSplit = native::RAR_OM_LIST_INCSPLIT,
}

// TODO: Move to unrar_sys?
#[repr(i32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Operation {
    Skip = native::RAR_SKIP,
    Test = native::RAR_TEST,
    Extract = native::RAR_EXTRACT,
}

macro_rules! mp_ext { () => (r"(\.part|\.r?)(\d+)((?:\.rar)?)$") }
lazy_static! {
    static ref MULTIPART_EXTENSION: Regex = Regex::new(mp_ext!()).unwrap();
    static ref EXTENSION: Regex = Regex::new(concat!(mp_ext!(), r"|\.rar$")).unwrap();
}

pub struct Archive<'a> {
    filename: Cow<'a, Path>,
    password: Option<&'a str>,
    read_comments: bool,
}

pub type Glob = PathBuf;

impl<'a> Archive<'a> {
    /// Creates an `Archive` object to operate on a plain RAR archive.
    pub fn new<T>(file: &'a T) -> Self
    where
        T: AsRef<Path> + ?Sized,
    {
        Archive {
            filename: Cow::Borrowed(file.as_ref()),
            password: None,
            read_comments: false,
        }
    }

    /// Creates an `Archive` object to operate on a password encrypted RAR archive.
    pub fn with_password<T, U>(file: &'a T, password: &'a U) -> Self
    where
        T: AsRef<Path> + ?Sized,
        U: AsRef<str> + ?Sized,
    {
        Archive {
            filename: Cow::Borrowed(file.as_ref()),
            password: Some(password.as_ref()),
            read_comments: false,
        }
    }

    /// Enable reading of the archive comments. File comments are not supported yet.
    // TODO: Decide on a better interface for this...
    pub fn enable_comments(&mut self) {
        self.read_comments = true;
    }

    /// Returns `true` if the filename matches a RAR archive.
    ///
    /// This method does not make any FS operations and operates purely on strings.
    pub fn is_archive(&self) -> bool {
        is_archive(&self.filename)
    }

    /// Returns `true` if the filename matches a part of a multipart collection, `false` otherwise
    ///
    /// This method does not make any FS operations and operates purely on strings.
    pub fn is_multipart(&self) -> bool {
        is_multipart(&self.filename)
    }

    /// Returns a glob string covering all parts of the multipart collection or `None`
    /// if the underlying archive is a single-part archive.
    ///
    /// This method does not make any FS operations and operates purely on strings.
    pub fn all_parts_option(&self) -> Option<Glob> {
        get_rar_extension(&self.filename).and_then(|full_ext| {
            MULTIPART_EXTENSION.captures(&full_ext).map(|captures| {
                let mut replacement = String::from(captures.get(1).unwrap().as_str());
                replacement.push_str(&repeat("?")
                                     .take(captures.get(2).unwrap().as_str().len())
                                     .collect::<String>());
                replacement.push_str(captures.get(3).unwrap().as_str());
                full_ext.replace(captures.get(0).unwrap().as_str(), &replacement)
            })
        }).and_then(|new_ext| {
            self.filename.file_stem().map(|x| Path::new(x).with_extension(&new_ext[1..]))
        })
    }

    /// Returns a glob string covering all parts of the multipart collection or
    /// a copy of the underlying archive's filename if it's a single-part archive.
    ///
    /// This method does not make any FS operations and operates purely on strings.
    pub fn all_parts(&self) -> Glob {
        match self.all_parts_option() {
            Some(x) => x,
            None => self.filename.to_path_buf(),
        }
    }

    /// Returns the nth part of this multi-part collection or `None`
    /// if the underlying archive is single part
    ///
    /// This method does not make any FS operations and operates purely on strings.
    pub fn nth_part(&self, n: i32) -> Option<PathBuf> {
        get_rar_extension(&self.filename).and_then(|full_ext| {
            MULTIPART_EXTENSION.captures(&full_ext).map(|captures| {
                let mut replacement = String::from(captures.get(1).unwrap().as_str());
                // `n` padded with zeroes to the length of archive's number's length
                replacement.push_str(&format!("{:01$}", n, captures.get(2).unwrap().as_str().len()));
                replacement.push_str(captures.get(3).unwrap().as_str());
                full_ext.replace(captures.get(0).unwrap().as_str(), &replacement)
            })
        }).and_then(|new_ext| {
            self.filename.file_stem().map(|x| Path::new(x).with_extension(&new_ext[1..]))
        })
    }

    /// Return the first part of the multipart collection or `None`
    /// if the underlying archive is single part
    ///
    /// This method does not make any FS operations and operates purely on strings.
    pub fn first_part_option(&self) -> Option<PathBuf> {
        self.nth_part(1)
    }

    /// Returns the first part of the multipart collection or
    /// a copy of the underlying archive's filename if it's a single-part archive.
    ///
    /// This method does not make any FS operations and operates purely on strings.
    pub fn first_part(&self) -> PathBuf {
        match self.nth_part(1) {
            Some(x) => x,
            None => self.filename.to_path_buf(),
        }
    }

    /// Changes the filename to point to the first part of the multipart collection.
    /// Does nothing if it is a single-part archive.
    ///
    /// This method does not make any FS operations and operates purely on strings.
    pub fn as_first_part(&mut self) {
        self.first_part_option().map(|fp| self.filename = Cow::Owned(fp));
    }

    /// Opens the underlying archive for listing its contents
    pub fn list(self) -> Result<OpenArchiveListIter, UnrarError<OpenArchive>> {
        self.open(OpenMode::List, None).map(|arc| arc.into_iter())
    }

    /// Opens the underlying archive for listing its contents
    /// without omitting or pooling split entries
    pub fn list_split(self) -> Result<OpenArchiveListIter, UnrarError<OpenArchive>> {
        self.open(OpenMode::ListSplit, None).map(|arc| arc.into_iter())

    }

    /// Opens the underlying archive in extract mode, allowing extraction of files, testing file integrity or reading its contents as bytes.
    pub fn extract(self) -> UnrarResult<OpenArchive> {
        self.open(OpenMode::Extract, None)
    }

    /// Opens the underlying archive in extract mode, with default destination.
    pub fn extract_to<P: AsRef<Path>>(self, destination: P) -> UnrarResult<OpenArchive> {
        self.open(OpenMode::Extract, Some(destination.as_ref()))
    }

    /// Opens the underlying archive with the provided parameters.
    fn open(self, mode: OpenMode, destination: Option<&Path>) -> UnrarResult<OpenArchive>
    {
        // Since OpenArchive::new is private let's just strip generics here.
        OpenArchive::new(&self.filename,
                         mode,
                         self.password,
                         self.read_comments,
                         destination)
    }
}


// Used for passing data to and from the RARProcessFile callback, and to UnprocessedEntry.
pub(crate) struct Shared {
    // read-only
    pub destination: Option<WideCString>,
    // read-only
    pub password: Option<WideCString>,
    // The next volume is written in the callback to this field, when a volume change is necessary.
    pub volume: Cell<Option<WideCString>>,
    // Bytes are written to this field over multiple calls of the callback.
    pub bytes: RefCell<Option<Vec<u8>>>,
    // Stores _temporary_ pointer to a user provided closure for reading entry bytes.
    // Care must be taken when using this, always make sure to replace the value before use.
    // Also preferably drop after use.
    pub bytes_closure: RefCell<Option<UnsafeBytesClosurePointer>>,
    // Transports panics in user provided closure outside FFI boundary for use in `resume_unwind`.
    pub bytes_closure_panic: Cell<Option<UnwindingPanic>>,
    // Transports errors in callback outside FFI boundary.
    pub callback_error: Cell<Option<ProvidedPasswordTooLong>>,
    // Transports fatal errors in callback outside FFI boundary so that we can try to panic.
    pub callback_panic: Cell<Option<CallbackPanic>>,
}
// Debug impl for Cell<T> requres T: Copy + Debug, which doesn't apply to all fields.
impl fmt::Debug for Shared {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("Shared")
            .field("destination", &self.destination)
            .field("password", &self.password)
            .field("volume", &"<NextVolumeString>")
            .field("bytes", &self.bytes)
            .field("bytes_closure", &self.bytes_closure)
            .field("bytes_closure_panic", &"<BytesClosurePanic>")
            .field("callback_error", &self.callback_error)
            .field("callback_panic", &self.callback_panic)
            .finish()
    }
}

pub(crate) type SharedData = Rc<Shared>;
type CallbackFn = Box<dyn Fn(native::UINT, native::LPARAM, native::LPARAM) -> CallbackControl>;
type BytesClosureFn = Box<dyn FnMut(&[u8]) -> CallbackControl>;
type UnwindingPanic = Box<dyn any::Any + Send + 'static>;

// Container for the user-provided closure pointer.
#[derive(Debug)]
pub(crate) struct UnsafeBytesClosurePointer(usize);
impl UnsafeBytesClosurePointer {
    pub fn new(callback: impl FnMut(&[u8]) -> CallbackControl) -> Self {
        // Hackery to bypass the unecessary static lifetime limitation for the closure.
        // Note: The casts are crucial!
        let raw_ptr = Box::into_raw(Box::new(Box::new(callback)
                                             as Box<dyn FnMut(&[u8]) -> CallbackControl>));
        debug_assert_eq!(mem::size_of_val(&raw_ptr), mem::size_of::<usize>());
        Self(raw_ptr as usize)
    }

    #[inline]
    pub fn call(&mut self, bytes: &[u8]) -> CallbackControl {
        debug_assert_eq!(mem::size_of_val(&self.0), mem::size_of::<*mut BytesClosureFn>());
        let ptr = self.0 as *mut BytesClosureFn;
        assert!(!ptr.is_null(), "Bytes closure pointer is null");
        let f = unsafe { &mut *ptr };
        f(bytes)
    }
}
impl Drop for UnsafeBytesClosurePointer {
    fn drop(&mut self) {
        drop(unsafe { Box::from_raw(self.0 as *mut BytesClosureFn) });
    }
}

/// Return value for controlling the processing callback.
pub enum CallbackControl {
    Abort = -1,
    Ignored = 0,
    Continue = 1,
}

// TODO: Shouldn't this be in unrar_sys...?
bitflags! {
    #[derive(Default)]
    struct ArchiveFlags: u32 {
        const VOLUME = native::ROADF_VOLUME;
        const COMMENT = native::ROADF_COMMENT;
        const LOCK = native::ROADF_LOCK;
        const SOLID = native::ROADF_SOLID;
        const NEW_NUMBERING = native::ROADF_NEWNUMBERING;
        const SIGNED = native::ROADF_SIGNED;
        const RECOVERY = native::ROADF_RECOVERY;
        const ENC_HEADERS = native::ROADF_ENCHEADERS;
        const FIRST_VOLUME = native::ROADF_FIRSTVOLUME;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VolumeInfo {
    None,
    First,
    Subsequent,
}

#[derive(Debug)]
pub struct OpenArchive {
    pub(crate) handle: NonNull<native::HANDLE>,
    comment: Option<String>,
    flags: ArchiveFlags,
    // used to share data between processing and callback
    pub(crate) shared: SharedData,
    callback_ptr: NonNull<CallbackFn>,
}

// TODO: Provide utility functions such as extract_all(dest)?
impl OpenArchive {
    fn new(filename: &Path,
           mode: OpenMode,
           password: Option<&str>,
           read_comments: bool,
           destination: Option<&Path>)
           -> UnrarResult<Self>
    {
        let password = match password {
            Some(pw) => Some(WideCString::from_str(pw)?),
            None => None,
        };
        let destination = match destination {
            Some(dest) => Some(WideCString::from_os_str(dest)?),
            None => None,
        };
        let filename = WideCString::from_os_str(&filename)?;

        let mut data = native::OpenArchiveDataEx::new(filename.as_ptr() as *const _,
                                                      mode as u32);

        // Sneaking in a Rust callback function as data pointer to the FFI callback,
        // making it easier to pass data to and from the ProcessFile event handler function.
        let shared = Rc::new(Shared {
            destination,
            password,
            volume: Cell::new(None),
            bytes: RefCell::new(None),
            bytes_closure: RefCell::new(None),
            bytes_closure_panic: Cell::new(None),
            callback_error: Cell::new(None),
            callback_panic: Cell::new(None),
        });
        let user_data_ref = shared.clone();
        // Trait object -> Thin pointer -> Raw pointer
        let boxed_callback: *mut CallbackFn = Box::into_raw(Box::new(Box::new(Self::callback_handler(user_data_ref))));
        debug_assert_eq!(mem::size_of_val(&boxed_callback), mem::size_of_val(&data.user_data),
                         "unrar_sys::LPARAM must match callback pointer size.");
        data.user_data = boxed_callback as native::LPARAM;
        data.callback = Some(Self::callback);

        if read_comments {
            // Max comment size is 256kb (as of unrar 5.00).
            // If comments don't fit this they get left out.
            let mut buffer = mem::ManuallyDrop::new(Vec::with_capacity(256_000 / mem::size_of::<u8>()));
            let ptr = buffer.as_mut_ptr();
            let cap = buffer.capacity();
            debug_assert_eq!(cap * mem::size_of::<u8>(), 256_000,
                             "Comment buffer should be 256kb");

            // TODO: Couldn't figure out how to use data.comment_buffer_w (access violation).
            debug_assert_eq!(mem::size_of_val(&ptr), mem::size_of_val(&data.comment_buffer),
                             "Comment buffer ptr size does not match the unrar_sys comment_buffer size.");
            data.comment_buffer = ptr as *mut _;
            data.comment_buffer_w = ptr::null_mut();
            data.comment_buffer_size = cap.try_into()?;
        }

        let handle = NonNull::new(unsafe { native::RAROpenArchiveEx(&mut data as *mut _) }
                                  as *mut _);
        let result = Code::from(data.open_result).unwrap();

        debug_assert!(shared.bytes_closure_panic.take().is_none());
        if let Some(err) = shared.callback_panic.take() {
            panic!("{:?}[{:?}]: {:?}", When::Open, result, err);
        } else if let Some(err) = shared.callback_error.take() {
            // FIXME: Could handle gracefully by returning the error.
            //return Err(Error::from_callback(err, When::Open))
            panic!("{:?}[{:?}]: {:?}", When::Open, result, err);
        }

        let comment = if read_comments {
            assert!(data.comment_size <= data.comment_buffer_size);
            let buffer = unsafe { Vec::from_raw_parts(data.comment_buffer as *mut _,
                                                      data.comment_size.try_into()?,
                                                      data.comment_buffer_size.try_into()?) };

            data.comment_buffer = ptr::null_mut();
            data.comment_buffer_w = ptr::null_mut();

            match data.comment_state {
                0 => { // No comments
                    debug_assert_eq!(data.comment_size, 0);
                    None
                },
                1 => Some(CStr::from_bytes_with_nul(buffer.as_slice())?
                          .to_str()?.to_owned()),
                // TODO: Could return truncated comment with error when ERAR_SMALL_BUF.
                _ => return Err(UnrarError::from(Code::from(data.comment_state)
                                                 .unwrap_or(Code::Unknown),
                                                 When::ReadComment))
            }
        } else { None };

        if let Some(handle) = handle {
            let archive = OpenArchive {
                handle,
                comment,
                shared,
                flags: ArchiveFlags::from_bits(data.flags).unwrap(),
                callback_ptr: NonNull::new(boxed_callback).unwrap(),
            };

            match result {
                Code::Success => Ok(archive),
                _ => Err(UnrarError::new(result, When::Open, archive)),
            }
        } else {
            Err(UnrarError::from(result, When::Open))
        }
    }

    /// No-frills interface for iterating archive entries.
    #[inline]
    pub fn reader(self) -> OpenArchiveReader {
        OpenArchiveReader::new(self)
    }

    /// Convert OpenArchive into a StreamingIterator.
    #[inline]
    pub fn iter<'a>(self) -> OpenArchiveStreamingIter<'a> {
        OpenArchiveStreamingIter::new(self)
    }

    pub fn is_locked(&self) -> bool {
        self.flags.contains(ArchiveFlags::LOCK)
    }

    pub fn has_encrypted_headers(&self) -> bool {
        self.flags.contains(ArchiveFlags::ENC_HEADERS)
    }

    pub fn has_recovery_record(&self) -> bool {
        self.flags.contains(ArchiveFlags::RECOVERY)
    }

    pub fn has_comment(&self) -> bool {
        self.flags.contains(ArchiveFlags::COMMENT)
    }

    /// Solid archive, all files in a single compressed block.
    pub fn is_solid(&self) -> bool {
        self.flags.contains(ArchiveFlags::SOLID)
    }

    /// Indicates whether the archive file is split into multiple volumes or not,
    /// and if so, whether the file is the first volume or not.
    pub fn volume_info(&self) -> VolumeInfo {
        if self.flags.contains(ArchiveFlags::FIRST_VOLUME) {
            VolumeInfo::First
        } else if self.flags.contains(ArchiveFlags::VOLUME) {
            VolumeInfo::Subsequent
        } else {
            VolumeInfo::None
        }
    }

    pub fn comment(&self) -> Option<&str> {
        self.comment.as_ref().map(|x| x.as_str())
    }

    extern "system" fn callback(msg: native::UINT, user_data: native::LPARAM,
                                p1: native::LPARAM, p2: native::LPARAM) -> c_int
    {
        panic::catch_unwind(move || {
            // println!("msg: {}, user_data: {:x}, p1: {:x}, p2: {}", msg, user_data, p1, p2);
            let ptr = user_data as *mut CallbackFn;
            assert!(!ptr.is_null(), "Callback function pointer is null");
            let f = unsafe { &mut *ptr };
            f(msg, p1, p2) as c_int
        }).unwrap_or_else(|_| {
            // Abort on panic, any panics that end up here ought to be bugs.
            process::abort();
        })
    }

    // TODO: Could return error messages using SharedData.
    fn callback_handler(user_data: SharedData)
                        -> impl Fn(native::UINT, native::LPARAM, native::LPARAM) -> CallbackControl
    {
        move |msg: native::UINT, p1: native::LPARAM, p2: native::LPARAM| {
            let callback_panic = |kind: CallbackPanicKind| -> CallbackControl {
                user_data.callback_panic.set(Some(CallbackPanic::new(kind)));
                CallbackControl::Abort
            };

            match msg {
                native::UCM_CHANGEVOLUMEW => {
                    let ptr = p1 as *const native::WCHAR;

                    // Prevent from_ptr_with_nul from panicking.
                    if ptr.is_null() { return callback_panic(CallbackPanicKind::NullVolume); }

                    // 2048 seems to be the buffer size in unrar,
                    // also it's the maximum path length since 5.00.
                    let next = unsafe { WideCString::from_ptr_truncate(ptr as *const _, 2048) };
                    user_data.volume.set(Some(next));

                    match p2 {
                        // Next volume not found.
                        native::RAR_VOL_ASK => CallbackControl::Abort,
                        // Next volume found.
                        _ => CallbackControl::Continue,
                    }
                },
                native::UCM_NEEDPASSWORDW if p2 > 0 => {
                    if let Some(pw) = user_data.password.as_ref() {
                        let ptr = p1 as *mut native::WCHAR;
                        let len = p2 as usize;

                        // Null password with non-zero length (p2 > 0).
                        if ptr.is_null() { return callback_panic(CallbackPanicKind::NullPassword); }

                        // slice::from_raw_parts_mut expects length to be under isize::MAX.
                        // Also len this large would be extremely unusual (expected value is 128).
                        if len > isize::MAX as usize {
                            return callback_panic(CallbackPanicKind::AnomalousPasswordLength(len, isize::MAX));
                        }

                        // Our current expectation from the underlying unrar library.
                        debug_assert!(len == 128,
                                      "Max password length should be 127 characters (127 + nul)");

                        let buf = unsafe { slice::from_raw_parts_mut(ptr as *mut _, len) };

                        let pw = pw.as_slice_with_nul();
                        if len >= pw.len() {
                            buf[..pw.len()].copy_from_slice(pw);
                            return CallbackControl::Continue;
                        } else {
                            user_data.callback_error
                                .replace(Some(ProvidedPasswordTooLong::new(pw.len(), len)));
                            return CallbackControl::Abort;
                        }
                    }
                    // No password provided.
                    CallbackControl::Abort
                },
                native::UCM_PROCESSDATA if p2 > 0 => {
                    let mut bytes_ref = match user_data.bytes.try_borrow_mut() {
                        Ok(bytes_ref) => bytes_ref,
                        Err(_) => return callback_panic(CallbackPanicKind::BytesBorrowed),
                    };
                    let mut closure_ref = match user_data.bytes_closure.try_borrow_mut() {
                        Ok(closure_ref) => closure_ref,
                        Err(_) => return callback_panic(CallbackPanicKind::BytesClosureBorrowed),
                    };

                    if let Some(vec) = bytes_ref.as_mut() {
                        let ptr = p1 as *const u8;
                        let len = p2 as usize;

                        // Null data buffer with non-zero length (p2 > 0).
                        if ptr.is_null() { return callback_panic(CallbackPanicKind::NullDataPointer); }

                        // slice::from_raw_parts_mut expects length to be under isize::MAX.
                        if len > isize::MAX as usize {
                            return callback_panic(CallbackPanicKind::DataBufferTooLarge(len, isize::MAX));
                        }

                        let bytes = unsafe { slice::from_raw_parts(ptr, len) };
                        vec.extend_from_slice(bytes);
                    } else if let Some(closure) = closure_ref.as_mut() {
                        let ptr = p1 as *const u8;
                        let len = p2 as usize;

                        // Null data buffer with non-zero length (p2 > 0).
                        if ptr.is_null() { return callback_panic(CallbackPanicKind::NullDataPointer); }

                        // slice::from_raw_parts_mut expects length to be under isize::MAX.
                        if len > isize::MAX as usize {
                            return callback_panic(CallbackPanicKind::DataBufferTooLarge(len, isize::MAX));
                        }

                        let bytes = unsafe { slice::from_raw_parts(ptr, len) };

                        let mut f = panic::AssertUnwindSafe(closure);
                        return panic::catch_unwind(move || f.call(bytes))
                            .unwrap_or_else(|err| {
                                user_data.bytes_closure_panic.set(Some(Box::new(err)));
                                CallbackControl::Abort
                            });
                    }
                    CallbackControl::Continue
                },
                _ => CallbackControl::Ignored, // Ignore msg and continue
            }
        }
    }
}


impl IntoIterator for OpenArchive {
    type Item = UnrarResult<Entry>;
    type IntoIter = OpenArchiveListIter;

    fn into_iter(self) -> Self::IntoIter {
        OpenArchiveListIter {
            inner: self,
            damaged: false,
        }
    }
}

impl Deref for OpenArchiveListIter {
    type Target = OpenArchive;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

/// List only iterator.
#[derive(Debug)]
pub struct OpenArchiveListIter {
    inner: OpenArchive,
    damaged: bool,
}

impl Iterator for OpenArchiveListIter {
    type Item = UnrarResult<Entry>;

    fn next(&mut self) -> Option<Self::Item> {
        // The damaged flag was set, don't attempt to read any further, stop
        if self.damaged {
            return None;
        }
        let mut header = native::HeaderDataEx::default();
        let read_result =
            Code::from(unsafe { native::RARReadHeaderEx(self.inner.handle.as_ptr(),
                                                        &mut header as *mut _) as u32 })
            .unwrap();
        match read_result {
            Code::Success => {
                let process_result = Code::from(unsafe {
                    native::RARProcessFileW(
                        self.inner.handle.as_ptr(),
                        Operation::Skip as i32,
                        ptr::null(),
                        ptr::null()
                    ) as u32
                }).unwrap();

                match process_result {
                    Code::Success | Code::EOpen => {
                        let mut entry = Entry::from(header);

                        // EOpen on Process: Next volume not found
                        if process_result == Code::EOpen {
                            entry.next_volume = self.inner.shared.volume
                                .take().map(|x| PathBuf::from(x.to_os_string()));
                            self.damaged = true;
                            Some(Err(UnrarError::new(process_result, When::Process, entry)))
                        } else {
                            Some(Ok(entry))
                        }
                    },
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

                        self.damaged = true;
                        Some(Err(UnrarError::from(process_result, When::Process)))
                    }
                }
            },
            Code::EndArchive => None,
            _ => {
                debug_assert!(self.shared.bytes_closure_panic.take().is_none());
                if let Some(err) = self.shared.callback_panic.take() {
                    panic!("{:?}[{:?}]: {:?}", When::Read, read_result, err);
                } else if let Some(err) = self.shared.callback_error.take() {
                    // FIXME: Could handle gracefully by returning the error.
                    //return Some(Err(Error::from_callback(err, When::Read)))
                    panic!("{:?}[{:?}]: {:?}", When::Read, read_result, err);
                }

                self.damaged = true;
                Some(Err(UnrarError::from(read_result, When::Read)))
            }
        }
    }
}

impl Drop for OpenArchive {
    fn drop(&mut self) {
        unsafe { native::RARCloseArchive(self.handle.as_ptr()); }
        debug_assert!(self.shared.bytes_closure_panic.take().is_none());
        debug_assert!(self.shared.callback_panic.take().is_none());

        let raw_ptr: *mut CallbackFn = self.callback_ptr.as_ptr();
        drop(unsafe { Box::from_raw(raw_ptr) });
    }
}


fn get_rar_extension<T: AsRef<Path>>(path: T) -> Option<String> {
    path.as_ref().extension().map(|ext| {
        let pre_ext = path.as_ref().file_stem().and_then(|x| Path::new(x).extension());
        match pre_ext {
            Some(pre_ext) => format!(".{}.{}", pre_ext.to_string_lossy(), ext.to_string_lossy()),
            None => format!(".{}", ext.to_string_lossy())
        }
    })
}

pub fn is_archive(s: &Path) -> bool {
    get_rar_extension(s).and_then(|full_ext| {
        EXTENSION.find(&full_ext).map(|_| ())
    }).is_some()
}

pub fn is_multipart(s: &Path) -> bool {
    get_rar_extension(s).and_then(|full_ext| {
        MULTIPART_EXTENSION.find(&full_ext).map(|_| ())
    }).is_some()
}

#[cfg(test)]
mod tests {
    use super::Archive;
    use std::path::PathBuf;

    #[test]
    fn glob() {
        assert_eq!(Archive::new("arc.part0010.rar").all_parts(),
                   PathBuf::from("arc.part????.rar"));
        assert_eq!(Archive::new("archive.r100").all_parts(),
                   PathBuf::from("archive.r???"));
        assert_eq!(Archive::new("archive.r9").all_parts(), PathBuf::from("archive.r?"));
        assert_eq!(Archive::new("archive.999").all_parts(),
                   PathBuf::from("archive.???"));
        assert_eq!(Archive::new("archive.rar").all_parts(),
                   PathBuf::from("archive.rar"));
        assert_eq!(Archive::new("random_string").all_parts(),
                   PathBuf::from("random_string"));
        assert_eq!(Archive::new("v8/v8.rar").all_parts(), PathBuf::from("v8/v8.rar"));
        assert_eq!(Archive::new("v8/v8").all_parts(), PathBuf::from("v8/v8"));
    }

    #[test]
    fn first_part() {
        assert_eq!(Archive::new("arc.part0010.rar").first_part(),
                   PathBuf::from("arc.part0001.rar"));
        assert_eq!(Archive::new("archive.r100").first_part(),
                   PathBuf::from("archive.r001"));
        assert_eq!(Archive::new("archive.r9").first_part(), PathBuf::from("archive.r1"));
        assert_eq!(Archive::new("archive.999").first_part(),
                   PathBuf::from("archive.001"));
        assert_eq!(Archive::new("archive.rar").first_part(),
                   PathBuf::from("archive.rar"));
        assert_eq!(Archive::new("random_string").first_part(),
                   PathBuf::from("random_string"));
        assert_eq!(Archive::new("v8/v8.rar").first_part(), PathBuf::from("v8/v8.rar"));
        assert_eq!(Archive::new("v8/v8").first_part(), PathBuf::from("v8/v8"));
    }

    #[test]
    fn is_archive() {
        assert_eq!(super::is_archive(&PathBuf::from("archive.rar")), true);
        assert_eq!(super::is_archive(&PathBuf::from("archive.part1.rar")), true);
        assert_eq!(super::is_archive(&PathBuf::from("archive.part100.rar")), true);
        assert_eq!(super::is_archive(&PathBuf::from("archive.r10")), true);
        assert_eq!(super::is_archive(&PathBuf::from("archive.part1rar")), false);
        assert_eq!(super::is_archive(&PathBuf::from("archive.rar\n")), false);
        assert_eq!(super::is_archive(&PathBuf::from("archive.zip")), false);
    }

    #[test]
    fn nul_in_input() {
        use crate::error::{Code, When};

        let err = Archive::new("\0archive.rar").list().unwrap_err();
        assert_eq!(err.code, Code::Unknown);
        assert_eq!(err.when, When::Open);

        let err = Archive::with_password("archive.rar", "un\0rar").list().unwrap_err();
        assert_eq!(err.code, Code::Unknown);
        assert_eq!(err.when, When::Open);
    }
}
