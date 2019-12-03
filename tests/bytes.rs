extern crate unrar;

use std::str;
use unrar::Archive;

#[test]
fn version_cat() {
    let bytes = &Archive::new("data/version.rar")
        .read_bytes("VERSION")
        .unwrap();
    let s = str::from_utf8(bytes).unwrap();
    assert_eq!(s, "unrar-0.4.0");
}

#[test]
fn bytes_eq_unpacked_size() {
    for entry in Archive::new("data/archive.part1.rar").list().unwrap()
        .filter(|e| e.as_ref().map(|e| !e.is_split()).unwrap_or(false))
        .map(|e| e.unwrap())
    {
        let bytes = &Archive::new("data/archive.part1.rar").read_bytes(entry.filename).unwrap();
        assert_eq!(bytes.len(), entry.unpacked_size);
    }
}
