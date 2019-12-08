extern crate unrar;

use std::str;
use unrar::Archive;

fn main() {
    println!(
        "{}",
        str::from_utf8(&Archive::new("version.rar")
            .read_entry_bytes("VERSION")
            .unwrap())
            .unwrap()
    );
}
