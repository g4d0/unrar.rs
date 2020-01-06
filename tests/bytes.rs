extern crate unrar;

use std::str;
use unrar::{Archive, Header, StreamingIterator};

#[test]
fn version_cat_streaming() {
    let bytes = &Archive::new("data/version.rar")
        .extract()
        .unwrap().iter()
        .next().unwrap().as_ref().unwrap().read_bytes().unwrap()
        .take_bytes().unwrap();
    let s = str::from_utf8(bytes).unwrap();
    assert_eq!(s, "unrar-0.4.0");
}

#[test]
fn version_cat_reader() {
    let bytes = &Archive::new("data/version.rar")
        .extract()
        .unwrap().reader()
        .read_next_header().unwrap().unwrap().read_bytes().unwrap()
        .take_bytes().unwrap();
    let s = str::from_utf8(bytes).unwrap();
    assert_eq!(s, "unrar-0.4.0");
}

#[test]
fn bytes_eq_unpacked_size_streaming() {
    let iter = Archive::new("data/archive.part1.rar").extract().unwrap().iter();
    iter.filter(|e| e.as_ref().map(|e| !e.is_split()).unwrap_or(false))
        .for_each(|e| {
            let entry = e.as_ref().unwrap().read_bytes().unwrap();
            assert_eq!(entry.bytes().unwrap().len(), entry.unpacked_size());
        });
}

#[test]
fn bytes_eq_unpacked_size_reader() {
    let mut iter = Archive::new("data/archive.part1.rar").extract().unwrap().reader();
    while let Some(e) = iter.read_next_header() {
        let entry = e.unwrap();
        if entry.is_split() { break; }
        let byts = entry.read_bytes().unwrap();
        assert_eq!(byts.bytes().unwrap().len(), byts.unpacked_size());
    }
}
