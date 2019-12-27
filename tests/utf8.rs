extern crate tempdir;
extern crate unrar;

use unrar::{Archive, Header, StreamingIterator};
use std::path::PathBuf;

#[test]
fn unicode_list() {
    let mut entries = Archive::new("data/unicode.rar").list().unwrap().into_iter();
    assert_eq!(entries.next().unwrap().unwrap().filename(), PathBuf::from("te…―st✌"));
}

#[test]
fn extract_utf8_password() {
    use tempdir::TempDir;
    use std::fs::File;
    use std::io::prelude::*;

    let t = TempDir::new("unrar").unwrap();
    Archive::with_password("data/utf8-password.rar", "utf🎱")
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
fn list_utf8_password_enc_headers() {
    let mut entries = Archive::with_password("data/utf8-password-encheader.rar", "utf🎱").list().unwrap().into_iter();
    assert_eq!(entries.next().unwrap().unwrap().filename(), PathBuf::from(".gitignore"));
}

#[test]
fn unicode_list_streaming() {
    let mut entries = Archive::new("data/unicode.rar").list().unwrap().iter();
    assert_eq!(entries.next().unwrap().as_ref().unwrap().filename(), PathBuf::from("te…―st✌"));
}

#[test]
fn foobar_list() {
    let mut entries = Archive::new("data/utf8.rar").list().unwrap().into_iter();
    assert_eq!(entries.next().unwrap().unwrap().filename(), PathBuf::from("foo—bar"));
}

#[test]
fn foobar_list_streaming() {
    let mut entries = Archive::new("data/utf8.rar").list().unwrap().iter();
    assert_eq!(entries.next().unwrap().as_ref().unwrap().filename(), PathBuf::from("foo—bar"));
}
