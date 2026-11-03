use std::path::{Path, PathBuf};

use preborrowck_mir::test_utils::Compile;

use super::check_all_bodies;

// The version of a crate the lockfile of `crates/` resolves. Fetching that manifest
// puts that copy in the registry of every machine that runs the tests.
fn locked_version(name: &str) -> String {
    let lockfile: PathBuf =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("src/tests/crates/Cargo.lock");
    let lock: String = std::fs::read_to_string(&lockfile).expect("`crates/` has a lockfile");
    lock.lines()
        .zip(lock.lines().skip(1))
        .filter_map(|(name_line, version_line)| {
            (name_line == format!("name = \"{name}\""))
                .then(|| version_line.strip_prefix("version = \"")?.strip_suffix('"'))
                .flatten()
        })
        .max_by_key(|version| {
            let numbers: Vec<u64> = version
                .split(['.', '-', '+'])
                .take(3)
                .map(|part| part.parse::<u64>().expect("a version starts with three numbers"))
                .collect();
            (numbers, !version.contains('-'))
        })
        .unwrap_or_else(|| panic!("the lockfile has `{name}`"))
        .to_owned()
}

// The copy of a crate in the local cargo registry at the version the lockfile resolves.
fn registry_crate(name: &str) -> PathBuf {
    let home: PathBuf = std::env::var_os("CARGO_HOME").map_or_else(
        || PathBuf::from(std::env::var_os("HOME").expect("HOME is set")).join(".cargo"),
        PathBuf::from,
    );
    let registry: PathBuf = home.join("registry").join("src");
    let directory: String = format!("{name}-{}", locked_version(name));
    std::fs::read_dir(&registry)
        .expect("the cargo registry has sources")
        .map(|index| index.expect("the registry index is readable").path().join(&directory))
        .find(|path| path.is_dir())
        .unwrap_or_else(|| panic!("the registry has `{directory}`"))
}

// The value of a key in a table of the manifest of a registry crate.
fn manifest_value(name: &str, table: &str, key: &str) -> Option<String> {
    let manifest: String = std::fs::read_to_string(registry_crate(name).join("Cargo.toml"))
        .expect("the registry crate has a manifest");
    let mut current: &str = "";
    for line in manifest.lines() {
        if let Some(header) = line.strip_prefix('[') {
            current = header.trim_end_matches(']');
        } else if let Some((k, value)) = line.split_once('=')
            && current == table
            && k.trim() == key
        {
            return Some(value.trim().trim_matches('"').to_owned());
        }
    }
    None
}

// The edition the manifest of a registry crate declares.
fn edition(name: &str) -> String {
    manifest_value(name, "package", "edition").unwrap_or_else(|| "2015".to_owned())
}

// The root file of the library of a registry crate.
fn lib_path(name: &str) -> PathBuf {
    let path: String =
        manifest_value(name, "lib", "path").unwrap_or_else(|| "src/lib.rs".to_owned());
    registry_crate(name).join(path)
}

fn assert_same_facts_in_crate(name: &str, features: &[&str]) {
    let root: PathBuf = lib_path(name);
    let mut args: Vec<String> = vec![format!("--edition={}", edition(name))];
    for feature in features {
        args.push("--cfg".to_owned());
        args.push(format!("feature=\"{feature}\""));
    }
    Compile { args, ..Compile::file(root) }.run(check_all_bodies);
}

#[test]
fn itoa() {
    assert_same_facts_in_crate("itoa", &[]);
}

#[test]
fn scopeguard() {
    assert_same_facts_in_crate("scopeguard", &["use_std"]);
}

#[test]
fn either() {
    assert_same_facts_in_crate("either", &["std"]);
}

#[test]
fn smallvec() {
    assert_same_facts_in_crate("smallvec", &[]);
}

#[test]
fn ryu() {
    assert_same_facts_in_crate("ryu", &[]);
}

#[test]
fn bitflags() {
    assert_same_facts_in_crate("bitflags", &[]);
}

#[test]
fn byteorder() {
    assert_same_facts_in_crate("byteorder", &["std"]);
}

#[test]
fn bit_vec() {
    assert_same_facts_in_crate("bit-vec", &["std"]);
}

#[test]
fn dary_heap() {
    assert_same_facts_in_crate("dary_heap", &[]);
}

#[test]
fn memchr() {
    assert_same_facts_in_crate("memchr", &["std", "alloc"]);
}

#[test]
fn base64() {
    assert_same_facts_in_crate("base64", &["std", "alloc"]);
}

#[test]
fn aho_corasick() {
    assert_same_facts_in_crate("aho-corasick", &[]);
}

#[test]
fn allocator_api2() {
    assert_same_facts_in_crate("allocator-api2", &["alloc", "std"]);
}

#[test]
fn anes() {
    assert_same_facts_in_crate("anes", &[]);
}

#[test]
fn anstyle() {
    assert_same_facts_in_crate("anstyle", &["std"]);
}

#[test]
fn anstyle_parse() {
    assert_same_facts_in_crate("anstyle-parse", &[]);
}

#[test]
fn autocfg() {
    assert_same_facts_in_crate("autocfg", &[]);
}

#[test]
fn bumpalo() {
    assert_same_facts_in_crate("bumpalo", &[]);
}

#[test]
fn bytemuck() {
    assert_same_facts_in_crate("bytemuck", &[]);
}

#[test]
fn cast() {
    assert_same_facts_in_crate("cast", &[]);
}

#[test]
fn ciborium_io() {
    assert_same_facts_in_crate("ciborium-io", &[]);
}

#[test]
fn clap_lex() {
    assert_same_facts_in_crate("clap_lex", &[]);
}

#[test]
fn colorchoice() {
    assert_same_facts_in_crate("colorchoice", &[]);
}

#[test]
fn daachorse() {
    assert_same_facts_in_crate("daachorse", &["alloc"]);
}

#[test]
fn encode_unicode() {
    assert_same_facts_in_crate("encode_unicode", &["std"]);
}

#[test]
fn escape8259() {
    assert_same_facts_in_crate("escape8259", &[]);
}

#[test]
fn fastrand() {
    assert_same_facts_in_crate("fastrand", &["alloc", "std"]);
}

#[test]
fn find_msvc_tools() {
    assert_same_facts_in_crate("find-msvc-tools", &[]);
}

#[test]
fn fnv() {
    assert_same_facts_in_crate("fnv", &["std"]);
}

#[test]
fn foldhash() {
    assert_same_facts_in_crate("foldhash", &["std"]);
}

#[test]
fn futures_core() {
    assert_same_facts_in_crate("futures-core", &["alloc", "std"]);
}

#[test]
fn futures_task() {
    assert_same_facts_in_crate("futures-task", &["alloc", "std"]);
}

#[test]
fn hashbrown() {
    assert_same_facts_in_crate("hashbrown", &[]);
}

#[test]
fn heck() {
    assert_same_facts_in_crate("heck", &[]);
}

#[test]
fn hermit_abi() {
    assert_same_facts_in_crate("hermit-abi", &[]);
}

#[test]
fn html_escape() {
    assert_same_facts_in_crate("html-escape", &["std"]);
}

#[test]
fn ident_case() {
    assert_same_facts_in_crate("ident_case", &[]);
}

#[test]
fn index_vec() {
    assert_same_facts_in_crate("index_vec", &[]);
}

#[test]
fn is_terminal_polyfill() {
    assert_same_facts_in_crate("is_terminal_polyfill", &[]);
}

#[test]
fn linux_raw_sys() {
    assert_same_facts_in_crate("linux-raw-sys", &["errno", "general", "std"]);
}

#[test]
fn litemap() {
    assert_same_facts_in_crate("litemap", &["alloc"]);
}

#[test]
fn log() {
    assert_same_facts_in_crate("log", &[]);
}

#[test]
fn minimal_lexical() {
    assert_same_facts_in_crate("minimal-lexical", &["std"]);
}

#[test]
fn once_cell() {
    assert_same_facts_in_crate("once_cell", &["alloc", "race", "std"]);
}

#[test]
fn oorandom() {
    assert_same_facts_in_crate("oorandom", &[]);
}

#[test]
fn pkg_config() {
    assert_same_facts_in_crate("pkg-config", &[]);
}

#[test]
fn potential_utf() {
    assert_same_facts_in_crate("potential_utf", &[]);
}

#[test]
fn r_efi() {
    assert_same_facts_in_crate("r-efi", &[]);
}

#[test]
fn rand_core() {
    assert_same_facts_in_crate("rand_core", &[]);
}

#[test]
fn regex_automata() {
    assert_same_facts_in_crate("regex-automata", &[]);
}

#[test]
fn regex_syntax() {
    assert_same_facts_in_crate(
        "regex-syntax",
        &[
            "std",
            "unicode",
            "unicode-age",
            "unicode-bool",
            "unicode-case",
            "unicode-gencat",
            "unicode-perl",
            "unicode-script",
            "unicode-segment",
        ],
    );
}

#[test]
fn rustc_hash() {
    assert_same_facts_in_crate("rustc-hash", &["std"]);
}

#[test]
fn shlex() {
    assert_same_facts_in_crate("shlex", &["std"]);
}

#[test]
fn slab() {
    assert_same_facts_in_crate("slab", &["std"]);
}

#[test]
fn smawk() {
    assert_same_facts_in_crate("smawk", &[]);
}

#[test]
fn strsim() {
    assert_same_facts_in_crate("strsim", &[]);
}

#[test]
fn textwrap() {
    assert_same_facts_in_crate("textwrap", &[]);
}

#[test]
fn tracing_core() {
    assert_same_facts_in_crate("tracing-core", &[]);
}

#[test]
fn unicode_ident() {
    assert_same_facts_in_crate("unicode-ident", &[]);
}

#[test]
fn unicode_segmentation() {
    assert_same_facts_in_crate("unicode-segmentation", &[]);
}

#[test]
fn unicode_width() {
    assert_same_facts_in_crate("unicode-width", &["cjk"]);
}

#[test]
fn unicode_categories() {
    assert_same_facts_in_crate("unicode_categories", &[]);
}

#[test]
fn unit_prefix() {
    assert_same_facts_in_crate("unit-prefix", &["std"]);
}

#[test]
fn utf8_iter() {
    assert_same_facts_in_crate("utf8_iter", &[]);
}

#[test]
fn utf8parse() {
    assert_same_facts_in_crate("utf8parse", &[]);
}

#[test]
fn uuid() {
    assert_same_facts_in_crate("uuid", &[]);
}
