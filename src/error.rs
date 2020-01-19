use native;
use widestring;
use std::result::Result;
use num::FromPrimitive;
use std::fmt;
use std::ffi;
use std::error;
use std::str;

enum_from_primitive! {
    #[derive(PartialEq, Eq, Debug, Clone, Copy)]
    #[repr(i32)]
    pub enum Code {
        Success = native::ERAR_SUCCESS,
        EndArchive = native::ERAR_END_ARCHIVE,
        NoMemory = native::ERAR_NO_MEMORY,
        BadData = native::ERAR_BAD_DATA,
        BadArchive = native::ERAR_BAD_ARCHIVE,
        UnknownFormat = native::ERAR_UNKNOWN_FORMAT,
        EOpen = native::ERAR_EOPEN,
        ECreate = native::ERAR_ECREATE,
        EClose = native::ERAR_ECLOSE,
        ERead = native::ERAR_EREAD,
        EWrite = native::ERAR_EWRITE,
        SmallBuf = native::ERAR_SMALL_BUF,
        Unknown = native::ERAR_UNKNOWN,
        MissingPassword = native::ERAR_MISSING_PASSWORD,
        // From the UnRARDLL docs:
        // When attempting to unpack a reference record (see RAR -oi switch),
        // source file for this reference was not found.
        // Entire archive needs to be unpacked to properly create file references.
        // This error is returned when attempting to unpack the reference
        // record without its source file.
        EReference = native::ERAR_EREFERENCE,
        BadPassword = native::ERAR_BAD_PASSWORD
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum When {
    Open,
    Read,
    ReadComment,
    Process,
}

impl Code {
    pub fn from(code: u32) -> Option<Self> {
        Code::from_u32(code)
    }
}

#[derive(PartialEq)]
pub struct UnrarError<T> {
    pub code: Code,
    pub when: When,
    pub data: Option<T>,
}

impl<T> fmt::Debug for UnrarError<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}@{:?}", self.code, self.when)?;
        write!(f, " ({})", self)
    }
}

impl<T> fmt::Display for UnrarError<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Code::*;
        use self::When::*;
        match (self.code, self.when) {
            (BadData, Open) => write!(f, "Archive header damaged"),
            (BadData, Read) => write!(f, "File header damaged"),
            (BadData, Process) => write!(f, "File CRC error"),
            (UnknownFormat, Open) => write!(f, "Unknown encryption"),
            (EOpen, Process) => write!(f, "Could not open next volume"),
            (UnknownFormat, _) => write!(f, "Unknown archive format"),
            (EOpen, _) => write!(f, "Could not open archive"),
            (NoMemory, _) => write!(f, "Not enough memory"),
            (BadArchive, _) => write!(f, "Not a RAR archive"),
            (ECreate, _) => write!(f, "Could not create file"),
            (EClose, _) => write!(f, "Could not close file"),
            (ERead, _) => write!(f, "Read error"),
            (EWrite, _) => write!(f, "Write error"),
            (SmallBuf, _) => write!(f, "Archive comment was truncated to fit to buffer"),
            (MissingPassword, _) => write!(f, "Password for encrypted archive not specified"),
            (EReference, _) => write!(f, "Cannot open file source for reference record"),
            (BadPassword, _) => write!(f, "Wrong password was specified"),
            (Unknown, _) => write!(f, "Unknown error"),
            (EndArchive, _) => write!(f, "Archive end"),
            (Success, _) => write!(f, "Success"),
            (_, _) => write!(f, "Unknown error - code: {:?}, when: {:?}", self.code, self.when),
        }
    }
}

impl<T> UnrarError<T> {
    pub fn new(code: Code, when: When, data: T) -> Self {
        UnrarError {
            code: code,
            when: when,
            data: Some(data),
        }
    }

    pub fn from(code: Code, when: When) -> Self {
        UnrarError {
            code: code,
            when: when,
            data: None,
        }
    }
}

pub type UnrarResult<T> = Result<T, UnrarError<T>>;

// TODO: Add proper error for these
impl<T, C: widestring::UChar> From<widestring::NulError<C>> for UnrarError<T> {
    fn from(_: widestring::NulError<C>) -> UnrarError<T> {
        UnrarError::from(Code::Unknown, When::Open)
    }
}

impl<T> From<ffi::FromBytesWithNulError> for UnrarError<T> {
    fn from(_: ffi::FromBytesWithNulError) -> UnrarError<T> {
        UnrarError::from(Code::Unknown, When::Open)
    }
}

impl<T> From<str::Utf8Error> for UnrarError<T> {
    fn from(_: str::Utf8Error) -> UnrarError<T> {
        UnrarError::from(Code::Unknown, When::Open)
    }
}


#[derive(Debug, Clone, Copy)]
pub enum CallbackPanicKind {
    NullVolume,
    NullPassword,
    NullDataPointer,
    VolumeMissingNul,
    AnomalousPasswordLength(usize, isize),
    DataBufferTooLarge(usize, isize),
}

impl fmt::Display for CallbackPanicKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            CallbackPanicKind::NullVolume => {
                write!(f, "pointer to next volume buffer is null")
            },
            CallbackPanicKind::NullPassword => {
                write!(f, "pointer to password buffer is null")
            },
            CallbackPanicKind::NullDataPointer => {
                write!(f, "pointer to data buffer is null")
            },
            CallbackPanicKind::VolumeMissingNul => {
                write!(f, "next volume string is missing nul terminator")
            },
            CallbackPanicKind::AnomalousPasswordLength(length, max) => {
                write!(f, "unusually large password buffer length ({}), should be less than {}",
                       length, max)
            },
            CallbackPanicKind::DataBufferTooLarge(length, max) => {
                write!(f, "data buffer larger than allowed ({}), should be less than {}",
                       length, max)
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct CallbackPanic(CallbackPanicKind);

impl CallbackPanic {
    pub fn new(kind: CallbackPanicKind) -> Self {
        Self(kind)
    }

    pub fn kind(&self) -> &CallbackPanicKind {
        &self.0
    }
}


/// User provided password was longer than what is supported by unrar.
#[derive(Debug, Clone, Copy)]
pub struct ProvidedPasswordTooLong(usize, usize);
impl ProvidedPasswordTooLong {
    pub fn new(length: usize, expected: usize) -> Self {
        ProvidedPasswordTooLong(length, expected)
    }
}

impl fmt::Display for ProvidedPasswordTooLong {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: length {}, expected less than or equal to {}",
               error::Error::description(self),
               self.0, self.1)
    }
}

impl error::Error for ProvidedPasswordTooLong {
    fn description(&self) -> &str {
        "password too long"
    }
}
