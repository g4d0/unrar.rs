extern crate unrar;

use std::path::PathBuf;

#[test]
fn foobar_list() {
    let mut entries = unrar::Archive::new("data/utf8.rar".into()).list().unwrap();
    assert_eq!(entries.next().unwrap().unwrap().filename, PathBuf::from("foo—bar"));
}
