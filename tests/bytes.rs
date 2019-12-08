extern crate unrar;

use std::str;
use unrar::{Archive, Header, StreamingIterator};

#[test]
fn version_cat() {
    let bytes = &Archive::new("data/version.rar")
        .read_entry_bytes("VERSION")
        .unwrap();
    let s = str::from_utf8(bytes).unwrap();
    assert_eq!(s, "unrar-0.4.0");
}

#[test]
fn version_cat_streaming() {
    let bytes = &Archive::new("data/version.rar")
        .read_bytes()
        .unwrap().iter()
        .next().unwrap().as_ref().unwrap().read_bytes().unwrap()
        .take_bytes().unwrap();
    let s = str::from_utf8(bytes).unwrap();
    assert_eq!(s, "unrar-0.4.0");
}

#[test]
fn bytes_eq_unpacked_size() {
    for entry in Archive::new("data/archive.part1.rar").list().unwrap().into_iter()
        .filter(|e| e.as_ref().map(|e| !e.is_split()).unwrap_or(false))
        .map(|e| e.unwrap())
    {
        let bytes = &Archive::new("data/archive.part1.rar").read_entry_bytes(entry.filename()).unwrap();
        assert_eq!(bytes.len(), entry.unpacked_size());
    }
}

#[test]
fn bytes_eq_unpacked_size_streaming() {
    let iter = Archive::new("data/archive.part1.rar").read_bytes().unwrap().iter();
    iter.filter(|e| e.as_ref().map(|e| !e.is_split()).unwrap_or(false))
        .for_each(|e| {
            let entry = e.as_ref().unwrap().read_bytes().unwrap();
            assert_eq!(entry.bytes().unwrap().len(), entry.unpacked_size());
        });
}
