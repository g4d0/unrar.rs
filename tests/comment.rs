extern crate unrar;

use unrar::Archive;
use unrar::error::{Code, When};

#[test]
fn archive_comment() {
    let mut archive = Archive::new("data/comment.rar");
    archive.enable_comments();
    let open_archive = archive.list().unwrap();
    assert!(open_archive.has_comment());
    assert_eq!(open_archive.comment().unwrap(), "abcdef12345\n");
}

#[test]
fn archive_comment_crypted() {
    let mut archive = Archive::with_password("data/comment-hpw-password.rar", "password");
    archive.enable_comments();
    let open_archive = archive.list().unwrap();
    assert!(open_archive.has_comment());
    assert_eq!(open_archive.comment().unwrap(), "abcdef12345\n");
}

// #[test]
// fn utf8_comment() {
//     let mut archive = Archive::new("data/comment-utf8.rar");
//     archive.enable_comments();
//     let open_archive = archive.list().unwrap();
//     assert!(open_archive.has_comment());
//     assert_eq!(open_archive.comment().unwrap(), "te…―st✌\n");
// }
