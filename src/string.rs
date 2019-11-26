use std::path::PathBuf;
use widestring::WideCString;

pub trait ToPathBuf {
    fn to_path_buf(&self) -> PathBuf;
}

pub trait ToWideCString {
    // TODO: Add error type for this.
    fn to_wide_cstring(&self) -> Option<WideCString>;
}

impl<T> ToWideCString for T where T: AsRef<std::ffi::OsStr> {
    fn to_wide_cstring(&self) -> Option<WideCString> {
        // Will copy. None if self contains nul values.
        WideCString::from_os_str(&self).ok()
    }
}

impl ToPathBuf for WideCString {
    fn to_path_buf(&self) -> PathBuf {
        // TODO: self can contain invalid UTF-16 data, does this cause issues on
        // non-windows platforms (where non-Unicode sequences get replaced with U+FFFD)?
        // Would it be better to fail here on such cases?
        PathBuf::from(self.to_os_string())
    }
}
