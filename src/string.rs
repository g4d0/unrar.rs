use std::path::{Path, PathBuf};
#[cfg(windows)]
use widestring::WideCString;
#[cfg(not(windows))]
use std::ffi::CString;

#[cfg(windows)]
mod os {
    use super::WideCString;

    #[derive(Debug)]
    pub struct InternalString(pub WideCString);
    pub type InternalStringType = WideCString;
}

#[cfg(not(windows))]
mod os {
    use super::CString;

    #[derive(Debug)]
    pub struct InternalString(pub CString);
    pub type InternalStringType = CString;
}

pub use self::os::InternalString;
pub use self::os::InternalStringType;

impl InternalString {
    pub fn new(inner: InternalStringType) -> Self {
        Self(inner)
    }
}

impl std::ops::Deref for InternalString {
    type Target = InternalStringType;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<&Path> for InternalString {
    fn from(path: &Path) -> InternalString {
        #[cfg(windows)]
        return InternalString::new(WideCString::from_os_str(path.as_os_str()).unwrap());
        #[cfg(unix)]
        {
            use std::ffi::OsStr;
            use std::os::unix::ffi::OsStrExt;
            return InternalString::new(CString::new(path.as_os_str().as_bytes()).unwrap());
        }
        #[cfg(not(any(unix, windows)))]
        return InternalString::new(CString::new(path.to_string_lossy().to_string().into_bytes()).unwrap());
    }
}

impl From<InternalString> for PathBuf {
    fn from(path: InternalString) -> PathBuf {
        #[cfg(windows)]
        return PathBuf::from(path.to_os_string());
        #[cfg(unix)]
        {
            use std::ffi::OsStr;
            use std::os::unix::ffi::OsStrExt;
            return PathBuf::from(OsStr::from_bytes(path.as_c_str().to_bytes()).to_os_string());
        }
        #[cfg(not(any(unix, windows)))]
        return PathBuf::from(path.to_str().unwrap());
    }
}
