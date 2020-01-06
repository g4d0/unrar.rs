extern crate unrar;

use std::str;
use std::path::Path;
use unrar::{Archive, Header, StreamingIterator};

fn main() {
    let mut iter = Archive::new("version.rar").extract().unwrap().iter();
    let entry = iter.find(|x| x.as_ref().unwrap().filename() == Path::new("VERSION"))
        .unwrap().as_ref().unwrap().read_bytes();
    println!("{}", str::from_utf8(entry.unwrap().bytes().unwrap()).unwrap());
}
