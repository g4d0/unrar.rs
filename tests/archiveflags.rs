extern crate unrar;

use unrar::Archive;
use unrar::archive::VolumeInfo;

#[test]
fn volume() {
    let archive = Archive::new("data/version.rar").list().unwrap();
    assert_eq!(archive.volume_info(), VolumeInfo::None);

    let archive = Archive::new("data/archive.part1.rar").list().unwrap();
    assert_eq!(archive.volume_info(), VolumeInfo::First);

    let archive = Archive::new("data/100M.part00002.rar").list().unwrap();
    assert_eq!(archive.volume_info(), VolumeInfo::Subsequent);
}

#[test]
fn locked() {
    let archive = Archive::new("data/locked.rar").list().unwrap();
    assert!(archive.is_locked());

    let archive = Archive::new("data/version.rar").list().unwrap();
    assert!(!archive.is_locked());
}

#[test]
fn recovery_record() {
    let archive = Archive::new("data/recovery-record.rar").list().unwrap();
    assert!(archive.has_recovery_record());

    let archive = Archive::new("data/version.rar").list().unwrap();
    assert!(!archive.has_recovery_record());
}

#[test]
fn archive_comment() {
    let archive = Archive::new("data/comment.rar").list().unwrap();
    assert!(archive.has_comment());

    let archive = Archive::new("data/version.rar").list().unwrap();
    assert!(!archive.has_comment());
}

#[test]
fn encrypted_headers() {
    // Will fail without password on open, with no err.data.
    let archive = Archive::with_password("data/comment-hpw-password.rar", "password").list().unwrap();
    assert!(archive.has_encrypted_headers());

    let archive = Archive::new("data/version.rar").list().unwrap();
    assert!(!archive.has_encrypted_headers());
}

#[test]
fn solid() {
    let archive = Archive::new("data/solid.rar").list().unwrap();
    assert!(archive.is_solid());

    let archive = Archive::new("data/version.rar").list().unwrap();
    assert!(!archive.is_solid());
}
