extern crate unrar;

use unrar::{Archive, StreamingIterator};

fn main() {
    Archive::new("archive.rar").extract_to("./archive").unwrap().iter()
        .for_each(|x| { x.as_ref().unwrap().extract().unwrap(); });
    println!("Done.");
}
