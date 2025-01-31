extern crate cc;

fn main() {
    cc::Build::new()
        .cpp(true) // Switch to C++ library compilation.
        .opt_level(2)
        .warnings(false)
        .flag_if_supported("-fPIC")
        .flag_if_supported("-Wno-switch")
        .flag_if_supported("-Wno-parentheses")
        .flag_if_supported("-Wno-macro-redefined")
        .flag_if_supported("-Wno-dangling-else")
        .flag_if_supported("-Wno-logical-op-parentheses")
        .flag_if_supported("-Wno-unused-parameter")
        .flag_if_supported("-Wno-unused-variable")
        .flag_if_supported("-Wno-unused-function")
        .flag_if_supported("-Wno-missing-braces")
        .flag_if_supported("-Wno-unknown-pragmas")
        .define("_FILE_OFFSET_BITS", Some("64"))
        .define("_LARGEFILE_SOURCE", None)
        .define("RAR_SMP", None)
        .define("RARDLL", None)
        .file("vendor/unrar/rar.cpp")
        .file("vendor/unrar/strlist.cpp")
        .file("vendor/unrar/strfn.cpp")
        .file("vendor/unrar/pathfn.cpp")
        .file("vendor/unrar/smallfn.cpp")
        .file("vendor/unrar/global.cpp")
        .file("vendor/unrar/file.cpp")
        .file("vendor/unrar/filefn.cpp")
        .file("vendor/unrar/filcreat.cpp")
        .file("vendor/unrar/archive.cpp")
        .file("vendor/unrar/arcread.cpp")
        .file("vendor/unrar/unicode.cpp")
        .file("vendor/unrar/system.cpp")
        .file("vendor/unrar/isnt.cpp")
        .file("vendor/unrar/crypt.cpp")
        .file("vendor/unrar/crc.cpp")
        .file("vendor/unrar/rawread.cpp")
        .file("vendor/unrar/encname.cpp")
        .file("vendor/unrar/resource.cpp")
        .file("vendor/unrar/match.cpp")
        .file("vendor/unrar/timefn.cpp")
        .file("vendor/unrar/rdwrfn.cpp")
        .file("vendor/unrar/consio.cpp")
        .file("vendor/unrar/options.cpp")
        .file("vendor/unrar/errhnd.cpp")
        .file("vendor/unrar/rarvm.cpp")
        .file("vendor/unrar/secpassword.cpp")
        .file("vendor/unrar/rijndael.cpp")
        .file("vendor/unrar/getbits.cpp")
        .file("vendor/unrar/sha1.cpp")
        .file("vendor/unrar/sha256.cpp")
        .file("vendor/unrar/blake2s.cpp")
        .file("vendor/unrar/hash.cpp")
        .file("vendor/unrar/extinfo.cpp")
        .file("vendor/unrar/extract.cpp")
        .file("vendor/unrar/volume.cpp")
        .file("vendor/unrar/list.cpp")
        .file("vendor/unrar/find.cpp")
        .file("vendor/unrar/unpack.cpp")
        .file("vendor/unrar/headers.cpp")
        .file("vendor/unrar/threadpool.cpp")
        .file("vendor/unrar/rs16.cpp")
        .file("vendor/unrar/cmddata.cpp")
        .file("vendor/unrar/ui.cpp")
        .file("vendor/unrar/filestr.cpp")
        .file("vendor/unrar/scantree.cpp")
        .file("vendor/unrar/dll.cpp")
        .file("vendor/unrar/qopen.cpp")
        .compile("libunrar.a");

    if cfg!(windows) {
        println!("cargo:rustc-link-lib=powrprof");
        println!("cargo:rustc-link-lib=shell32");
        println!("cargo:rustc-link-lib=user32");
        if cfg!(target_env = "gnu") {
            println!("cargo:rustc-link-lib=pthread");
        }
    } else {
        println!("cargo:rustc-link-lib=pthread");
    }
}
