extern crate tempdir;
extern crate unrar;

use unrar::{Archive, Header, StreamingIterator};
use unrar::error::{Code, When};
use tempdir::TempDir;
use std::fs::File;
use std::io::prelude::*;
use std::path::PathBuf;

#[test]
fn list() {
    // No password needed in order to list contents
    let mut entries = Archive::new("data/crypted.rar").list().unwrap().into_iter();
    assert_eq!(entries.next().unwrap().unwrap().filename(), PathBuf::from(".gitignore"));
}

#[test]
fn list_streaming() {
    // No password needed in order to list contents
    let mut entries = Archive::new("data/crypted.rar").extract().unwrap().iter();
    assert_eq!(entries.next().unwrap().as_ref().unwrap().filename(), PathBuf::from(".gitignore"));
}

#[test]
fn list_reader() {
    // No password needed in order to list contents
    let mut entries = Archive::new("data/crypted.rar").extract().unwrap().reader();
    assert_eq!(entries.read_next_header().unwrap().unwrap().filename(), PathBuf::from(".gitignore"));
}

#[test]
fn no_password_streaming() {
    let t = TempDir::new("unrar").unwrap();
    let mut arc = Archive::new("data/crypted.rar")
        .extract_to(t.path())
        .unwrap().iter();
    let err = arc.next().unwrap().as_ref().unwrap().extract().unwrap_err();
    assert_eq!(err.code, Code::MissingPassword);
    assert_eq!(err.when, When::Process);
}

#[test]
fn no_password_reader() {
    let t = TempDir::new("unrar").unwrap();
    let mut arc = Archive::new("data/crypted.rar")
        .extract_to(t.path())
        .unwrap().reader();
    let err = arc.read_next_header().unwrap().unwrap().extract().unwrap_err();
    assert_eq!(err.code, Code::MissingPassword);
    assert_eq!(err.when, When::Process);
}

#[test]
fn version_cat() {
    let t = TempDir::new("unrar").unwrap();
    Archive::with_password("data/crypted.rar", "unrar")
        .extract_to(t.path())
        .unwrap()
        .iter().for_each(|x| { x.as_ref().unwrap().extract().unwrap(); });
    let mut file = File::open(t.path().join(".gitignore")).unwrap();
    let mut s = String::new();
    file.read_to_string(&mut s).unwrap();
    assert_eq!(s, "target\nCargo.lock\n");
}

#[test]
fn list_encrypted_headers() {
    let mut entries = Archive::with_password("data/comment-hpw-password.rar", "password").list().unwrap();
    assert_eq!(entries.next().unwrap().unwrap().filename(), PathBuf::from(".gitignore"));
}

#[test]
fn no_password_list_encrypted_headers() {
    // Password needed in order to list contents
    let err = Archive::new("data/comment-hpw-password.rar").list().unwrap_err();
    assert_eq!(err.code, Code::MissingPassword);
    assert_eq!(err.when, When::Open);
    assert!(err.data.is_none());
}

#[test]
fn extract_encrypted_headers() {
    let t = TempDir::new("unrar").unwrap();
    Archive::with_password("data/comment-hpw-password.rar", "password")
        .extract_to(t.path())
        .unwrap()
        .iter().for_each(|x| { x.as_ref().unwrap().extract().unwrap(); });
    let mut file = File::open(t.path().join(".gitignore")).unwrap();
    let mut s = String::new();
    file.read_to_string(&mut s).unwrap();
    assert_eq!(s, "target\nCargo.lock\n");
}

#[test]
fn max_len_pw() {
    let t = TempDir::new("unrar").unwrap();
    Archive::with_password("data/max-len-password.rar", &"x".repeat(127))
        .extract_to(t.path())
        .unwrap()
        .iter().for_each(|x| { x.as_ref().unwrap().extract().unwrap(); });
    let mut file = File::open(t.path().join(".gitignore")).unwrap();
    let mut s = String::new();
    file.read_to_string(&mut s).unwrap();
    assert_eq!(s, "target\nCargo.lock\n");
}

#[test]
fn too_long_pw() {
    let t = TempDir::new("unrar").unwrap();
    let mut entries = Archive::with_password("data/max-len-password.rar", &"x".repeat(128))
        .extract_to(t.path())
        .unwrap()
        .iter();
    let err = entries.next().unwrap().as_ref().unwrap().extract().unwrap_err();
    assert_eq!(err.code, Code::MissingPassword);
    assert_eq!(err.when, When::Process);
}
