use native;
use widestring::WideCString;
use regex::Regex;
use std::os::raw::c_int;
use std::str;
use std::borrow::Cow;
use std::path::{Path, PathBuf};
use std::ffi::CStr;
use std::iter::repeat;
use std::slice;
use std::ptr::NonNull;
use std::boxed::Box;
use std::rc::Rc;
use std::cell::RefCell;

use crate::error::*;
use crate::entry::*;
use crate::streaming::*;
use crate::reader::*;

#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpenMode {
    List = native::RAR_OM_LIST,
    Extract = native::RAR_OM_EXTRACT,
    ListSplit = native::RAR_OM_LIST_INCSPLIT,
}

#[repr(i32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RAROperation {
    Skip = native::RAR_SKIP,
    Test = native::RAR_TEST,
    Extract = native::RAR_EXTRACT,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Operation {
    Skip,
    Test,
    Extract,
    Bytes,
}

impl From<Operation> for RAROperation {
    fn from(op: Operation) -> RAROperation {
        match op {
            Operation::Skip => RAROperation::Skip,
            Operation::Test => RAROperation::Test,
            Operation::Bytes => RAROperation::Test,
            Operation::Extract => RAROperation::Extract,
        }
    }
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
    pub fn list(self) -> UnrarResult<OpenArchive> {
        self.open::<&str>(OpenMode::List, None, Operation::Skip)
    }

    /// Opens the underlying archive for listing its contents
    /// without omitting or pooling split entries
    pub fn list_split(self) -> UnrarResult<OpenArchive> {
        self.open::<&str>(OpenMode::ListSplit, None, Operation::Skip)
    }

    /// Opens the underlying archive for extracting to the given directory.
    pub fn extract_to<T: AsRef<Path>>(self, path: T) -> UnrarResult<OpenArchive> {
        self.open(OpenMode::Extract, Some(path), Operation::Extract)
    }

    /// Opens the underlying archive for reading its contents as bytes.
    pub fn read_bytes(self) -> UnrarResult<OpenArchive> {
        self.open::<&str>(OpenMode::Extract, None, Operation::Bytes)
    }

    /// Opens the underlying archive for testing.
    pub fn test(self) -> UnrarResult<OpenArchive> {
        self.open::<&str>(OpenMode::Extract, None, Operation::Test)
    }

    /// Opens the underlying archive with the provided parameters.
    pub fn open<T: AsRef<Path>>(self,
                mode: OpenMode,
                path: Option<T>,
                operation: Operation)
                -> UnrarResult<OpenArchive> {
        // Since OpenArchive::new is private let's just strip generics here.
        OpenArchive::new(&self.filename, mode,
                         self.password,
                         self.read_comments,
                         path.as_ref().map(|x| x.as_ref()),
                         operation)
    }

    /// Returns the bytes for a particular file.
    pub fn read_entry_bytes<T: AsRef<Path>>(self, entry: T) -> Result<Vec<u8>, UnrarError<OpenArchive>> {
        self.open::<&str>(OpenMode::Extract, None, Operation::Test)?.read_bytes(entry)
    }
}


// Used for passing data to and from the RARProcessFile callback, and to UnprocessedEntry.
#[derive(Debug)]
pub(crate) struct Shared {
    pub destination: Option<WideCString>,
    pub password: Option<WideCString>,
    pub volume: RefCell<Option<WideCString>>,
    pub bytes: RefCell<Option<Vec<u8>>>,
}

pub(crate) type SharedData = Rc<Shared>;
type CallbackFn = Box<dyn FnMut(native::UINT, native::LPARAM, native::LPARAM) -> c_int>;

// TODO: Shouldn't this be in unrar_sys...?
bitflags! {
    #[derive(Default)]
    pub struct ArchiveFlags: u32 {
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

#[derive(Debug)]
pub struct OpenArchive {
    pub(crate) handle: NonNull<native::HANDLE>,
    operation: Operation,
    comment: Option<String>,
    flags: ArchiveFlags,
    // used to share data between processing and callback
    pub(crate) user_data: SharedData,
    callback_ptr: NonNull<CallbackFn>,
}

// TODO: Could be nice to allow reusing OpenArchive, to better facilitate use cases such as listing
// archive and operating on files out of order.
// Unsure if there's any meaningful gains though, as simply doing Archive::new and skipping to a
// file is plenty fast.
impl OpenArchive {
    fn new(filename: &Path,
           mode: OpenMode,
           password: Option<&str>,
           read_comments: bool,
           destination: Option<&Path>,
           operation: Operation)
           -> UnrarResult<Self>
    {
        let password = match password {
            Some(pw) => Some(WideCString::from_str(pw)?),
            None => None,
        };
        let destination = match destination {
            Some(dest) => Some(WideCString::from_os_str(&dest)?),
            None => None,
        };
        let filename = WideCString::from_os_str(&filename)?;

        let mut data = native::OpenArchiveDataEx::new(filename.as_ptr() as *const _,
                                                      mode as u32);

        // Sneaking in a Rust callback function as data pointer to the FFI callback,
        // making it easier to pass the real user data to the ProcessFile event handler function.
        // Also giving way the possibility of letting users of this library pass their own
        // closures as callbacks.
        let user_data = Rc::new(Shared {
            destination,
            password,
            volume: RefCell::new(None),
            bytes: RefCell::new(None),
        });
        let user_data_ref = user_data.clone();
        // Trait object -> Thin pointer -> Raw pointer
        let boxed_callback = Box::into_raw(Box::new(Box::new(Self::callback_handler(user_data_ref))
                                                    as CallbackFn));
        data.user_data = boxed_callback as native::LPARAM;
        data.callback = Some(Self::callback);

        if read_comments {
            // Max comment size is 256kb (as of unrar 5.00).
            // If comments don't fit this they get left out.
            let mut buffer = Vec::with_capacity(256_000 / std::mem::size_of::<u8>());
            let ptr = buffer.as_mut_ptr();
            let cap = buffer.capacity();
            debug_assert!(cap * std::mem::size_of::<u8>() == 256_000,
                          "Archive comment buffer should be 256kb not {}.",
                          cap * std::mem::size_of::<u8>());

            // TODO: Couldn't figure out how to use data.comment_buffer_w
            data.comment_buffer = ptr as *mut _;
            data.comment_buffer_size = cap as _;
            std::mem::forget(buffer);
        }

        let handle = NonNull::new(unsafe { native::RAROpenArchiveEx(&mut data as *mut _) }
                                  as *mut _);
        let result = Code::from(data.open_result).unwrap();

        let comment = if read_comments {
            assert!(data.comment_size <= data.comment_buffer_size);
            let buffer = unsafe { Vec::from_raw_parts(data.comment_buffer as *mut _,
                                                      data.comment_size as usize,
                                                      data.comment_buffer_size as usize) };
            data.comment_buffer = std::ptr::null_mut();

            match data.comment_state {
                0 => { // No comments
                    debug_assert!(data.comment_size == 0);
                    None
                },
                1 => Some(CStr::from_bytes_with_nul(buffer.as_slice())?
                          .to_str()?.to_owned()),
                _ => return Err(UnrarError::from(Code::from(data.comment_state)
                                                 .unwrap_or(Code::Unknown),
                                                 When::ReadComment))
            }
        } else { None };

        if let Some(handle) = handle {
            let archive = OpenArchive {
                handle: handle,
                comment: comment,
                flags: ArchiveFlags::from_bits(data.flags).unwrap(),
                operation: operation,
                user_data: user_data,
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

    /// Archive is part of a multivolume set, but not the first volume.
    pub fn is_volume(&self) -> bool {
        self.flags.contains(ArchiveFlags::VOLUME)
    }

    /// Archive is the first volume of a multivolume set.
    pub fn is_first_volume(&self) -> bool {
        self.flags.contains(ArchiveFlags::FIRST_VOLUME)
    }

    pub fn comment(&self) -> Option<&str> {
        self.comment.as_ref().map(|x| x.as_str())
    }

    pub fn process(self) -> UnrarResult<Vec<Entry>> {
        let (ts, es): (Vec<_>, Vec<_>) = self.into_iter().partition(|x| x.is_ok());
        let mut results: Vec<_> = ts.into_iter().map(|x| x.unwrap()).collect();
        match es.into_iter().map(|x| x.unwrap_err()).next() {
            Some(error) => {
                error.data.map(|x| results.push(x));
                Err(UnrarError::new(error.code, error.when, results))
            }
            None => Ok(results),
        }
    }

    extern "system" fn callback(msg: native::UINT, user_data: native::LPARAM,
                                p1: native::LPARAM, p2: native::LPARAM) -> c_int
    {
        std::panic::catch_unwind(move || {
            //println!("msg: {}, user_data: {}, p1: {}, p2: {}", msg, user_data, p1, p2);
            let ptr = user_data as *mut CallbackFn;
            assert!(!ptr.is_null());
            let f = unsafe { &mut *ptr };
            f(msg, p1, p2)
        }).unwrap_or_else(|_e| {
            #[cfg(debug_assertions)]
            eprintln!("{:?}", _e);

            std::process::abort();
        })
    }

    // TODO: Could return error messages using SharedData.
    fn callback_handler(user_data: SharedData)
                        -> impl FnMut(native::UINT, native::LPARAM, native::LPARAM) -> c_int
    {
        move |msg: native::UINT, p1: native::LPARAM, p2: native::LPARAM| {
            match msg {
                native::UCM_CHANGEVOLUMEW => {
                    let ptr = p1 as *const native::WCHAR;
                    if ptr.is_null() { return -1 }

                    // 2048 seems to be the buffer size in unrar,
                    // also it's the maximum path length since 5.00.
                    // TODO: Report on error
                    if let Ok(next) = unsafe { WideCString::from_ptr_with_nul(ptr as *const _, 2048) } {
                        user_data.volume.borrow_mut().replace(next);
                    }

                    match p2 {
                        // Next volume not found. -1 means stop
                        native::RAR_VOL_ASK => -1,
                        // Next volume found, 1 means continue
                        _ => 1,
                    }
                },
                native::UCM_NEEDPASSWORDW if p2 > 0 => {
                    if let Some(ref pw) = user_data.password {
                        let ptr = p1 as *mut native::WCHAR;
                        let len = p2 as usize;

                        assert!(!ptr.is_null(), "Got null pointer to buffer with non-zero length");
                        // This is an assert, because len this large would be
                        // extremely unusual (expected value is 128).
                        assert!(len <= std::isize::MAX as usize,
                                "slice::from_raw_parts_mut expects length to be under {}, got {}",
                                std::isize::MAX, len);

                        // Our current expectation from the underlying unrar library.
                        debug_assert!(len == 128,
                                      "Max password length should be 127 characters (127 + nul)");

                        let buf = unsafe { slice::from_raw_parts_mut(ptr as *mut _, len) };

                        let pw = pw.as_slice_with_nul();
                        // TODO: Pass a proper error message through user_data.
                        if len >= pw.len() {
                            buf[..pw.len()].copy_from_slice(pw);
                            return 1;
                        }
                    }
                    -1
                },
                native::UCM_PROCESSDATA if p2 > 0 => {
                    if let Some(vec) = user_data.bytes.borrow_mut().as_mut() {
                        let ptr = p1 as *const u8;
                        let len = p2 as usize;

                        assert!(!ptr.is_null(), "Got null pointer to buffer with non-zero length");
                        // TODO: Pass a proper error message through user_data.
                        if len > std::isize::MAX as usize { return -1 }
                        let bytes = unsafe { slice::from_raw_parts(ptr, len) };

                        vec.extend_from_slice(bytes);
                    }
                    1
                },
                _ => 1, // Ignore msg and continue
            }
        }
    }

    pub fn read_bytes<T: AsRef<Path>>(self, entry_filename: T) -> Result<Vec<u8>, UnrarError<OpenArchive>> {
        loop {
            let mut header = native::HeaderDataEx::default();
            let read_result =
                Code::from(unsafe { native::RARReadHeaderEx(self.handle.as_ptr(), &mut header as *mut _) }
                           as u32).unwrap();
            match read_result {
                Code::Success => {
                    let entry = Entry::from(header);
                    if entry.filename() != entry_filename.as_ref() {
                        let process_result = Code::from(unsafe {
                            native::RARProcessFile(
                                self.handle.as_ptr(),
                                Operation::Skip as i32,
                                0 as *const _,
                                0 as *const _
                                ) as u32 }).unwrap();
                        match process_result {
                            Code::Success => continue,
                            _ => return Err(UnrarError::new(process_result, When::Process, self))
                        }
                    }

                    // Try to reserve the full unpacked size ahead of time.
                    // Since apparently we can only read max dictionary size at a time
                    // with the callback.
                    //
                    // Max dictionary size is 4MB for RAR 3.x and 4.x,
                    // and 256MB (32bit) or 1GB (64bit) for RAR 5.0.
                    self.user_data.bytes.borrow_mut()
                        .replace(Vec::with_capacity(entry.unpacked_size()));

                    let process_result = Code::from(unsafe {
                        native::RARProcessFile(
                            self.handle.as_ptr(),
                            Operation::Test as i32,
                            0 as *const _,
                            0 as *const _
                            ) as u32 }).unwrap();
                    match process_result {
                        Code::Success => break,
                        _ => return Err(UnrarError::new(process_result, When::Process, self))
                    }
                }
                _ => return Err(UnrarError::new(read_result, When::Read, self))
            }
        }
        Ok(self.user_data.bytes.borrow_mut().take().unwrap())
    }
}


impl IntoIterator for OpenArchive {
    type Item = UnrarResult<Entry>;
    type IntoIter = OpenArchiveIter;

    fn into_iter(self) -> Self::IntoIter {
        OpenArchiveIter {
            inner: self,
            damaged: false,
        }
    }
}

pub struct OpenArchiveIter {
    inner: OpenArchive,
    damaged: bool,
}

impl Iterator for OpenArchiveIter {
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
                if self.inner.operation == Operation::Bytes {
                    self.inner.user_data.bytes.borrow_mut()
                        .replace(Vec::with_capacity(unpack_unp_size(header.unp_size,
                                                                    header.unp_size_high)));
                }

                let process_result = Code::from(unsafe {
                    native::RARProcessFileW(
                        self.inner.handle.as_ptr(),
                        RAROperation::from(self.inner.operation) as i32,
                        self.inner.user_data.destination.as_ref().map(
                            |x| x.as_ptr() as *const _
                        ).unwrap_or(0 as *const _),
                        0 as *const _
                    ) as u32
                }).unwrap();

                match process_result {
                    Code::Success | Code::EOpen => {
                        let mut entry = Entry::from(header);

                        if self.inner.operation == Operation::Bytes {
                            entry.bytes = match self.inner.user_data.bytes.borrow_mut().take() {
                                Some(bytes) => Some(bytes),
                                None => {
                                    self.damaged = true;
                                    return Some(Err(UnrarError::new(Code::Success, When::Process, entry)))
                                }
                            };
                        }

                        // EOpen on Process: Next volume not found
                        if process_result == Code::EOpen {
                            entry.next_volume = self.inner.user_data.volume.borrow_mut()
                                .take().map(|x| PathBuf::from(x.to_os_string()));
                            self.damaged = true;
                            Some(Err(UnrarError::new(process_result, When::Process, entry)))
                        } else {
                            Some(Ok(entry))
                        }
                    }
                    _ => {
                        self.damaged = true;
                        Some(Err(UnrarError::from(process_result, When::Process)))
                    }
                }
            }
            Code::EndArchive => None,
            _ => {
                self.damaged = true;
                Some(Err(UnrarError::from(read_result, When::Read)))
            }
        }
    }
}

impl Drop for OpenArchive {
    fn drop(&mut self) {
        unsafe {
            native::RARCloseArchive(self.handle.as_ptr());
            drop(Box::from_raw(self.callback_ptr.as_ptr() as *mut CallbackFn));
        }
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

        let err = Archive::new("archive.rar").extract_to("tmp/\0").unwrap_err();
        assert_eq!(err.code, Code::Unknown);
        assert_eq!(err.when, When::Open);
    }
}
