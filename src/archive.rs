use native;
use widestring::WideCString;
use regex::Regex;
use std::os::raw::c_int;
use std::str;
use std::fmt;
use std::path::{Path, PathBuf};
use std::ffi::CString;
use std::iter::repeat;
use std::slice;
use std::ptr::NonNull;
use error::*;
use string::*;

#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpenMode {
    List = native::RAR_OM_LIST,
    Extract = native::RAR_OM_EXTRACT,
    ListSplit = native::RAR_OM_LIST_INCSPLIT,
}

#[repr(i32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Operation {
    Skip = native::RAR_SKIP,
    Test = native::RAR_TEST,
    Extract = native::RAR_EXTRACT,
}

macro_rules! mp_ext { () => (r"(\.part|\.r?)(\d+)((?:\.rar)?)$") }
lazy_static! {
    static ref MULTIPART_EXTENSION: Regex = Regex::new(mp_ext!()).unwrap();
    static ref EXTENSION: Regex = Regex::new(concat!(mp_ext!(), r"|\.rar$")).unwrap();
}

pub struct Archive {
    filename: PathBuf,
    password: Option<String>,
}

pub type Glob = PathBuf;

impl Archive {
    /// Creates an `Archive` object to operate on a plain RAR archive.
    pub fn new(file: PathBuf) -> Self {
        Archive {
            filename: file,
            password: None,
        }
    }

    /// Creates an `Archive` object to operate on a password encrypted RAR archive.
    pub fn with_password(file: PathBuf, password: String) -> Self {
        Archive {
            filename: file,
            password: Some(password),
        }
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
            None => self.filename.clone(),
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
            None => self.filename.clone(),
        }
    }

    /// Changes the filename to point to the first part of the multipart collection.
    /// Does nothing if it is a single-part archive.
    ///
    /// This method does not make any FS operations and operates purely on strings.
    pub fn as_first_part(&mut self) {
        self.first_part_option().map(|fp| self.filename = fp);
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
        // TODO: Maybe let user know when CString construction fails...
        let password = self.password.and_then(|x| CString::new(x).ok());

        OpenArchive::new(self.filename, mode, password, path, operation)
    }

    /// Returns the bytes for a particular file.
    pub fn read_bytes<T: AsRef<Path>>(self, entry: T) -> Result<Vec<u8>, UnrarError<OpenArchive>> {
        self.open::<&str>(OpenMode::Extract, None, Operation::Test)?.read_bytes(entry)
    }
}

#[derive(Debug)]
pub struct OpenArchive {
    handle: NonNull<native::HANDLE>,
    operation: Operation,
    destination: Option<WideCString>,
    damaged: bool,
}

impl OpenArchive {
    fn new<T: AsRef<Path>, U: AsRef<Path>>(filename: T,
           mode: OpenMode,
           password: Option<CString>,
           destination: Option<U>,
           operation: Operation)
           -> UnrarResult<Self>
    {
        let filename = filename.as_ref().to_wide_cstring().unwrap();
        let mut data = native::OpenArchiveDataEx::new(filename.as_ptr() as *const _,
                                                      mode as u32);
        let handle = NonNull::new(unsafe { native::RAROpenArchiveEx(&mut data as *mut _) }
                                  as *mut _);
        let result = Code::from(data.open_result).unwrap();

        if let Some(handle) = handle {
            if let Some(pw) = password {
                unsafe { native::RARSetPassword(handle.as_ptr(), pw.as_ptr() as *const _) }
            }

            let archive = OpenArchive {
                handle: handle,
                destination: destination.and_then(|p| p.as_ref().to_wide_cstring()),
                damaged: false,
                operation: operation,
            };

            match result {
                Code::Success => Ok(archive),
                _ => Err(UnrarError::new(result, When::Open, archive)),
            }
        } else {
            Err(UnrarError::from(result, When::Open))
        }
    }

    pub fn process(&mut self) -> UnrarResult<Vec<Entry>> {
        let (ts, es): (Vec<_>, Vec<_>) = self.partition(|x| x.is_ok());
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
                                p1: native::LPARAM, p2: native::LPARAM) -> c_int {
        // println!("msg: {}, user_data: {}, p1: {}, p2: {}", msg, user_data, p1, p2);
        match msg {
            native::UCM_CHANGEVOLUMEW => {
                let ptr = p1 as *const _;
                // 2048 seems to be the buffer size in unrar,
                // also it's the maximum path length since 5.00.
                let next = unsafe { WideCString::from_ptr_with_nul(ptr, 2048) }.ok();
                let our_option = unsafe { &mut *(user_data as *mut enum_primitive::Option<WideCString>) };
                *our_option = next;
                match p2 {
                    // Next volume not found. -1 means stop
                    native::RAR_VOL_ASK => -1,
                    // Next volume found, 1 means continue
                    _ => 1,
                }
            }
            _ => 0,
        }
    }

    extern "system" fn callback_bytes(msg: native::UINT, user_data: native::LPARAM,
                                      p1: native::LPARAM, p2: native::LPARAM) -> c_int {
        //println!("msg: {}, user_data: {}, p1: {}, p2: {}", msg, user_data, p1, p2);
        match msg {
            native::UCM_PROCESSDATA if p2 > 0 => {
                let vec = unsafe { &mut *(user_data as *mut Vec<u8>) };
                let ptr = p1 as *const _;
                let bytes = unsafe { slice::from_raw_parts(ptr, p2 as usize) };
                vec.extend_from_slice(bytes);
                1
            }
            _ => -1,
        }
    }

    pub fn read_bytes<T: AsRef<Path>>(self, entry_filename: T) -> Result<Vec<u8>, UnrarError<OpenArchive>> {
        let mut bytes = Vec::new();
        loop {
            let mut header = native::HeaderDataEx::default();
            let read_result =
                Code::from(unsafe { native::RARReadHeaderEx(self.handle.as_ptr(), &mut header as *mut _) }
                           as u32).unwrap();
            match read_result {
                Code::Success => {
                    let entry = Entry::from(header);
                    if entry.filename != entry_filename.as_ref() {
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
                    bytes.reserve_exact(entry.unpacked_size);

                    // So we have the right entry, now set the
                    // callback and read it
                    unsafe {
                        native::RARSetCallback(self.handle.as_ptr(),
                                               Self::callback_bytes,
                                               &mut bytes as *mut _ as native::LPARAM)
                    }
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
        Ok(bytes)
    }
}

impl Iterator for OpenArchive {
    type Item = UnrarResult<Entry>;

    fn next(&mut self) -> Option<Self::Item> {
        // The damaged flag was set, don't attempt to read any further, stop
        if self.damaged {
            return None;
        }
        let mut volume: Option<WideCString> = None;
        unsafe {
            native::RARSetCallback(self.handle.as_ptr(), Self::callback, &mut volume as *mut _ as native::LPARAM)
        }
        let mut header = native::HeaderDataEx::default();
        let read_result =
            Code::from(unsafe { native::RARReadHeaderEx(self.handle.as_ptr(), &mut header as *mut _) as u32 })
                .unwrap();
        match read_result {
            Code::Success => {
                let process_result = Code::from(unsafe {
                    native::RARProcessFileW(
                        self.handle.as_ptr(),
                        self.operation as i32,
                        self.destination.as_ref().map(
                            |x| x.as_ptr() as *const _
                        ).unwrap_or(0 as *const _),
                        0 as *const _
                    ) as u32
                }).unwrap();

                match process_result {
                    Code::Success | Code::EOpen => {
                        let mut entry = Entry::from(header);
                        // EOpen on Process: Next volume not found
                        if process_result == Code::EOpen {
                            entry.next_volume = volume.map(|x| x.to_path_buf());
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
        }
    }
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
    pub filename: PathBuf,
    pub flags: EntryFlags,
    pub unpacked_size: usize,
    pub file_crc: u32,
    pub file_time: u32,
    pub method: u32,
    pub file_attr: u32,
    pub next_volume: Option<PathBuf>,
}

impl Entry {
    pub fn is_split(&self) -> bool {
        self.flags.contains(EntryFlags::SPLIT_BEFORE) || self.flags.contains(EntryFlags::SPLIT_AFTER)
    }

    pub fn is_directory(&self) -> bool {
        self.flags.contains(EntryFlags::DIRECTORY)
    }

    pub fn is_encrypted(&self) -> bool {
        self.flags.contains(EntryFlags::ENCRYPTED)
    }

    pub fn is_file(&self) -> bool {
        !self.is_directory()
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
            filename: filename.to_path_buf(),
            flags: EntryFlags::from_bits(header.flags).unwrap(),
            unpacked_size: header.unp_size as usize,
            file_crc: header.file_crc,
            file_time: header.file_time,
            method: header.method,
            file_attr: header.file_attr,
            next_volume: None,
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
        assert_eq!(Archive::new("arc.part0010.rar".into()).all_parts(),
                   PathBuf::from("arc.part????.rar"));
        assert_eq!(Archive::new("archive.r100".into()).all_parts(),
                   PathBuf::from("archive.r???"));
        assert_eq!(Archive::new("archive.r9".into()).all_parts(), PathBuf::from("archive.r?"));
        assert_eq!(Archive::new("archive.999".into()).all_parts(),
                   PathBuf::from("archive.???"));
        assert_eq!(Archive::new("archive.rar".into()).all_parts(),
                   PathBuf::from("archive.rar"));
        assert_eq!(Archive::new("random_string".into()).all_parts(),
                   PathBuf::from("random_string"));
        assert_eq!(Archive::new("v8/v8.rar".into()).all_parts(), PathBuf::from("v8/v8.rar"));
        assert_eq!(Archive::new("v8/v8".into()).all_parts(), PathBuf::from("v8/v8"));
    }

    #[test]
    fn first_part() {
        assert_eq!(Archive::new("arc.part0010.rar".into()).first_part(),
                   PathBuf::from("arc.part0001.rar"));
        assert_eq!(Archive::new("archive.r100".into()).first_part(),
                   PathBuf::from("archive.r001"));
        assert_eq!(Archive::new("archive.r9".into()).first_part(), PathBuf::from("archive.r1"));
        assert_eq!(Archive::new("archive.999".into()).first_part(),
                   PathBuf::from("archive.001"));
        assert_eq!(Archive::new("archive.rar".into()).first_part(),
                   PathBuf::from("archive.rar"));
        assert_eq!(Archive::new("random_string".into()).first_part(),
                   PathBuf::from("random_string"));
        assert_eq!(Archive::new("v8/v8.rar".into()).first_part(), PathBuf::from("v8/v8.rar"));
        assert_eq!(Archive::new("v8/v8".into()).first_part(), PathBuf::from("v8/v8"));
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
}
