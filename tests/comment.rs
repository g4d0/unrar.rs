extern crate unrar;

use unrar::Archive;

#[test]
fn archive_comment() {
    let mut archive = Archive::new("data/comment.rar");
    archive.enable_comments();
    let open_archive = archive.list().unwrap();
    assert_eq!(open_archive.comment().unwrap(), "abcdef12345\n");
}

// // Requires that UCM_NEEDPASSWORDW is implemented.
// #[test]
// fn archive_comment_crypted() {
//     let mut archive = Archive::with_password("data/comment-hpw-password.rar", "password");
//     archive.enable_comments();
//     let open_archive = archive.list().unwrap();
//     assert_eq!(open_archive.comment().unwrap(), "abcdef12345\n");
// }
