extern crate unrar_sys as native;
extern crate regex;
extern crate num;
#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate enum_primitive;
#[macro_use]
extern crate bitflags;
extern crate widestring;
extern crate streaming_iterator;

pub use archive::Archive;
pub use entry::Header;
pub use streaming::StreamingIterator;

pub mod error;
pub mod archive;
pub mod entry;
pub mod streaming;
pub mod reader;
