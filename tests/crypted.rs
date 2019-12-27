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
    let mut entries = Archive::new("data/crypted.rar").list().unwrap().iter();
    assert_eq!(entries.next().unwrap().as_ref().unwrap().filename(), PathBuf::from(".gitignore"));
}

#[test]
fn no_password() {
    let t = TempDir::new("unrar").unwrap();
    let mut arc = Archive::new("data/crypted.rar")
        .extract_to(t.path())
        .unwrap().into_iter();
    let err = arc.next().unwrap().unwrap_err();
    assert_eq!(err.code, Code::MissingPassword);
    assert_eq!(err.when, When::Process);
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
fn version_cat() {
    let t = TempDir::new("unrar").unwrap();
    Archive::with_password("data/crypted.rar", "unrar")
        .extract_to(t.path())
        .unwrap()
        .process()
        .unwrap();
    let mut file = File::open(t.path().join(".gitignore")).unwrap();
    let mut s = String::new();
    file.read_to_string(&mut s).unwrap();
    assert_eq!(s, "target\nCargo.lock\n");
}

#[test]
fn list_hp() {
    let mut entries = Archive::with_password("data/hpw-password.rar", "password").list().unwrap().into_iter();
    assert_eq!(entries.next().unwrap().unwrap().filename(), PathBuf::from(".gitignore"));
}

#[test]
fn no_password_list_hp() {
    // Password needed in order to list contents, when both header and contents encrypted.
    let err = Archive::new("data/hpw-password.rar").list().unwrap_err();
    assert_eq!(err.code, Code::MissingPassword);
    assert_eq!(err.when, When::Open);
    assert!(err.data.is_none());
}

#[test]
fn list_enc_headers_no_pw() {
    let err = Archive::new("data/utf8-password-encheader.rar").list().unwrap_err();
    assert_eq!(err.code, Code::MissingPassword);
    assert_eq!(err.when, When::Open);
}
