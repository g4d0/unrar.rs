extern crate unrar;

use std::path::PathBuf;
use std::rc::Rc;
use std::cell::RefCell;
use unrar::error::{Code, When};
use unrar::{Archive, Header, archive::CallbackControl};

// How it would look if the closure for read_bytes_with was required to be 'static (and RefUnwindSafe).
#[test]
fn read_bytes_static() {
    let mut archive = Archive::new("data/version.rar").extract().unwrap().reader();
    let string: Rc<RefCell<Option<String>>> = Rc::new(RefCell::new(None));

    //let string_ref = std::panic::AssertUnwindSafe(string.clone());
    let string_ref = string.clone();
    let entry = archive.read_next_header().unwrap().unwrap()
        .read_bytes_with(move |bytes| {
            string_ref.borrow_mut().replace(std::str::from_utf8(bytes).unwrap().to_string());
            assert_eq!(string_ref.borrow().as_ref().unwrap(), "unrar-0.4.0");
            CallbackControl::Continue
        }).unwrap();
    assert_eq!(entry.filename(), PathBuf::from("VERSION"));
    assert_eq!(string.borrow().as_ref().unwrap(), "unrar-0.4.0");
}

#[test]
fn read_bytes() {
    let mut archive = Archive::new("data/version.rar").extract().unwrap().reader();
    let mut string = None;

    let entry = archive.read_next_header().unwrap().unwrap()
        .read_bytes_with(|bytes| {
            string.replace(std::str::from_utf8(bytes).unwrap().to_string());
            assert_eq!(string.as_ref().unwrap(), "unrar-0.4.0");
            CallbackControl::Continue
        }).unwrap();
    assert_eq!(entry.filename(), PathBuf::from("VERSION"));
    assert_eq!(entry.dict_size(), 1);
    assert_eq!(string.as_ref().unwrap(), "unrar-0.4.0");
}

#[test]
fn read_bytes_multiple_calls_1mb() {
    let mut archive = Archive::new("data/1M-dict-64KB.rar").extract().unwrap().reader();
    let mut counter = 0;
    let mut data = Vec::new();

    let entry = archive.read_next_header().unwrap().unwrap()
        .read_bytes_with(|bytes| {
            counter += 1;
            data.extend_from_slice(bytes);
            assert!(1_048_576 > bytes.len());
            assert!(bytes.iter().all(|&x| x==0));
            CallbackControl::Continue
        }).unwrap();

    assert_eq!(entry.filename(), PathBuf::from("1M.dat"));
    assert_eq!(entry.unpacked_size(), data.len());
    assert_eq!(counter, 8);
}

#[test]
fn read_bytes_multiple_calls_10mb() {
    let mut archive = Archive::new("data/10M-dict-1MB.rar").extract().unwrap().reader();
    let mut counter = 0;
    let mut data = Vec::new();

    let entry = archive.read_next_header().unwrap().unwrap()
        .read_bytes_with(|bytes| {
            counter += 1;
            data.extend_from_slice(bytes);
            assert!(10_485_760 > bytes.len());
            assert!(bytes.iter().all(|&x| x==0));
            CallbackControl::Continue
        }).unwrap();

    assert_eq!(entry.filename(), PathBuf::from("10M.dat"));
    assert_eq!(entry.unpacked_size(), data.len());
    assert_eq!(counter, 20);
}

#[test]
fn user_callback_abort() {
    let mut archive = Archive::new("data/version.rar").extract().unwrap().reader();
    let err = archive.read_next_header().unwrap().unwrap()
        .read_bytes_with(|_| CallbackControl::Abort).unwrap_err();
    assert_eq!(err.code, Code::Unknown);
    assert_eq!(err.when, When::Process);
}

#[test]
#[should_panic]
fn panic_in_user_callback() {
    let mut archive = Archive::new("data/version.rar").extract().unwrap().reader();
    let _ = archive.read_next_header().unwrap().unwrap()
        .read_bytes_with(|_| panic!("test"));
}
