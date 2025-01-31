extern crate unrar;

use unrar::{Archive, Header, StreamingIterator};
use unrar::error::{Code, When};
use std::path::PathBuf;

#[test]
fn list_missing_volume() {
    let expected: Vec<PathBuf> = vec!["build.rs",
                                      "Cargo.toml",
                                      "examples/lister.rs",
                                      "src/lib.rs",
                                      "vendor/unrar/acknow.txt",
                                      "vendor/unrar/arccmt.cpp"].iter().map(|x| x.into()).collect();
    let mut archive = Archive::new("data/archive.part1.rar").list().unwrap().into_iter();
    for (i, e) in archive.by_ref().enumerate().take(expected.len()) {
        assert_eq!(e.unwrap().filename(), expected[i]);
    }
    let err = archive.next().unwrap().err().unwrap();
    assert_eq!(err.code, Code::EOpen);
    assert_eq!(err.when, When::Process);
    let data = err.data.unwrap();
    assert_eq!(data.filename(), PathBuf::from("vendor/unrar/archive.cpp"));
    assert_eq!(PathBuf::from(data.next_volume().unwrap()), PathBuf::from("data/archive.part2.rar"));
}

#[test]
fn list_missing_volume_streaming() {
    let expected: Vec<PathBuf> = vec!["build.rs",
                                      "Cargo.toml",
                                      "examples/lister.rs",
                                      "src/lib.rs",
                                      "vendor/unrar/acknow.txt",
                                      "vendor/unrar/arccmt.cpp"].iter().map(|x| x.into()).collect();
    let mut archive = Archive::new("data/archive.part1.rar").extract().unwrap().iter();
    let mut take = archive.by_ref().take(expected.len());
    let mut i = 0;
    while let Some(e) = take.next() {
        assert_eq!(e.as_ref().unwrap().filename(), expected[i]);
        i+=1;
    }
    let err = archive.next().unwrap().as_ref().unwrap().skip().err().unwrap();
    assert_eq!(err.code, Code::EOpen);
    assert_eq!(err.when, When::Process);
    let data = err.data.unwrap();
    assert_eq!(data.filename(), PathBuf::from("vendor/unrar/archive.cpp"));
    assert_eq!(PathBuf::from(data.next_volume().unwrap()), PathBuf::from("data/archive.part2.rar"));
}

#[test]
fn list_missing_volume_reader() {
    let expected: Vec<PathBuf> = vec!["build.rs",
                                      "Cargo.toml",
                                      "examples/lister.rs",
                                      "src/lib.rs",
                                      "vendor/unrar/acknow.txt",
                                      "vendor/unrar/arccmt.cpp"].iter().map(|x| x.into()).collect();
    let mut archive = Archive::new("data/archive.part1.rar").extract().unwrap().reader();
    let mut i = 0;
    while let Some(e) = archive.read_next_header() {
        assert_eq!(e.unwrap().skip().unwrap().filename(), expected[i]);
        i+=1;
        if i >= expected.len() { break; }
    }
    let err = archive.read_next_header().unwrap().unwrap().skip().err().unwrap();
    assert_eq!(err.code, Code::EOpen);
    assert_eq!(err.when, When::Process);
    let data = err.data.unwrap();
    assert_eq!(data.filename(), PathBuf::from("vendor/unrar/archive.cpp"));
    assert_eq!(PathBuf::from(data.next_volume().unwrap()), PathBuf::from("data/archive.part2.rar"));
}
