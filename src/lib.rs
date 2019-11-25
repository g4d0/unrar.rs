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

pub use archive::Archive;
pub mod error;
pub mod archive;
mod string;
