extern crate tempdir;
extern crate unrar;

use tempdir::TempDir;
use std::fs::File;
use std::io::prelude::*;
use std::path::PathBuf;
use unrar::{Archive, Header, StreamingIterator};

#[test]
fn version_list() {
    let mut entries = Archive::new("data/version.rar").list().unwrap();
    assert_eq!(entries.next().unwrap().unwrap().filename(), PathBuf::from("VERSION"));
}

#[test]
fn version_list_streaming() {
    let mut entries = Archive::new("data/version.rar").extract().unwrap().iter();
    assert_eq!(entries.next().unwrap().as_ref().unwrap().filename(), PathBuf::from("VERSION"));
}

#[test]
fn version_list_reader() {
    let mut entries = Archive::new("data/version.rar").extract().unwrap().reader();
    let head = entries.read_next_header().unwrap();
    assert_eq!(head.unwrap().skip().unwrap().filename(), PathBuf::from("VERSION"));
}

#[test]
fn version_cat() {
    let t = TempDir::new("unrar").unwrap();
    Archive::new("data/version.rar")
        .extract_to(t.path())
        .unwrap()
        .iter().for_each(|x| { x.as_ref().unwrap().extract().unwrap(); });
    let mut file = File::open(t.path().join("VERSION")).unwrap();
    let mut s = String::new();
    file.read_to_string(&mut s).unwrap();
    assert_eq!(s, "unrar-0.4.0");
}

#[test]
fn version_cat_entry_dest() {
    let t = TempDir::new("unrar").unwrap();
    Archive::new("data/version.rar")
        .extract()
        .unwrap()
        .iter().for_each(|x| { x.as_ref().unwrap().extract_to(t.path()).unwrap(); });
    let mut file = File::open(t.path().join("VERSION")).unwrap();
    let mut s = String::new();
    file.read_to_string(&mut s).unwrap();
    assert_eq!(s, "unrar-0.4.0");
}
