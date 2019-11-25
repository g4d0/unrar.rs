use std::path::{Path, PathBuf};
use widestring::WideCString;

#[derive(Debug)]
pub struct InternalString(pub WideCString);
pub type InternalStringType = WideCString;

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
        InternalString::new(WideCString::from_os_str(path.as_os_str()).unwrap())
    }
}

impl From<InternalString> for PathBuf {
    fn from(path: InternalString) -> PathBuf {
        PathBuf::from(path.to_os_string())
    }
}
