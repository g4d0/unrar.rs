extern crate unrar;

use unrar::{Archive, Header, StreamingIterator};
use std::path::PathBuf;

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
