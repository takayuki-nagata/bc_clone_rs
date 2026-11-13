// SPDX-License-Identifier: MIT

//! Tests of the scanner on fixtures.

use super::*;
use std::collections::BTreeMap;

/// Files in memory, keyed by their path relative to the repository root.
struct Mem(BTreeMap<PathBuf, String>);

impl Mem {
    fn new(files: &[(&str, &str)]) -> Self {
        Mem(files
            .iter()
            .map(|(p, t)| (PathBuf::from(p), t.to_string()))
            .collect())
    }
}

impl Source for Mem {
    fn read(&self, path: &Path) -> Option<String> {
        self.0.get(&normalize(path)).cloned()
    }
    fn exists(&self, path: &Path) -> bool {
        self.0.contains_key(&normalize(path))
    }
}

const CORE: usize = 0;
/// A crate whose tests Miri does not run.
const QEMU: usize = 4;

fn scan_one(krate: usize, files: &[(&str, &str)]) -> (Scan, Mem) {
    let src = Mem::new(files);
    let mut s = Scan::default();
    scan_crate(&src, krate, &mut s);
    resolve(&mut s, &src);
    (s, src)
}

fn item<'a>(s: &'a Scan, name: &str) -> &'a Item {
    s.items
        .iter()
        .find(|i| i.name == name)
        .unwrap_or_else(|| panic!("no item {name} in {:?}", names(s)))
}

fn names(s: &Scan) -> Vec<String> {
    s.items.iter().map(|i| i.name.clone()).collect()
}

#[test]
fn cfg_decides_what_is_production_code_and_what_is_a_test() {
    let (s, _) = scan_one(
        CORE,
        &[(
            "crates/bc_core/src/lib.rs",
            r#"
pub fn always() {}
#[cfg(test)]
fn only_tests() {}
#[cfg(not(test))]
fn not_tests() {}
#[cfg(any(test, kani))]
fn tests_or_kani() {}
#[cfg(feature = "std")]
fn feature_gated() {}
#[cfg(verus_keep_ghost)]
fn ghost_only() {}
#[cfg(test)]
mod tests {
    #[test]
    fn runs() { always(); }
    #[test]
    #[cfg_attr(miri, ignore)]
    fn ignored_under_miri() { always(); }
    #[test]
    #[cfg(not(miri))]
    fn not_under_miri() { always(); }
    #[test]
    #[ignore]
    fn ignored() { always(); }
}
#[cfg(kani)]
mod proofs {
    #[kani::proof]
    fn harness() { always(); }
}
"#,
        )],
    );
    assert_eq!(names(&s), ["always", "not_tests", "feature_gated"]);
    let tests: Vec<&str> = s.miri_tests.iter().map(|t| t.name.as_str()).collect();
    assert_eq!(tests, ["runs"]);
    let harnesses: Vec<&str> = s.harnesses.iter().map(|t| t.name.as_str()).collect();
    assert_eq!(harnesses, ["harness"]);
}

#[test]
fn tests_of_a_crate_that_miri_does_not_run_do_not_count() {
    let (s, _) = scan_one(
        QEMU,
        &[("crates/bc_qemu_riscv32/src/main.rs", "#[test] fn t() {}")],
    );
    assert!(s.miri_tests.is_empty());
}

#[test]
fn verus_items_are_classified_by_mode_and_attributes() {
    let (s, _) = scan_one(
        CORE,
        &[(
            "crates/bc_core/src/lib.rs",
            r#"
verus! {
pub fn plain(x: u8) -> (r: u8)
    ensures
        match r { 0 => true, _ => true },
{
    proof { assume(x < 3); }
    x
}
pub open spec fn s(x: int) -> int { x }
proof fn p() { admit(); }
pub axiom fn ax(x: int) ensures x == x;
pub uninterp spec fn u(x: int) -> int;
#[verifier::external_body]
fn wrapper(b: &[u8]) -> (r: Vec<u8>) ensures r@ == b@ { b.to_vec() }
#[verifier::external_body]
pub fn bare() { }
#[verifier::exec_allows_no_decreases_clause]
fn spins() { loop {} }
#[verifier::external_body]
pub struct Opaque { x: u8 }
#[verifier::external_type_specification]
pub struct ExT(T);
pub assume_specification[ <T as Clone>::clone ](t: &T) -> (r: T) ensures r == *t;
impl<'a> Holder<'a> {
    pub fn get(&self) -> u8 { 0 }
}
impl Clone for Thing {
    fn clone(&self) -> Self { Thing }
}
pub trait Tr {
    fn decl(&self);
    fn default_m(&self) -> u8 { 1 }
}
pub struct Normal { x: u8 }
#[cfg(test)]
fn test_only() {}
}
"#,
        )],
    );
    let kind = |n: &str| item(&s, n).kind;
    assert_eq!(kind("plain"), KIND_EXEC);
    assert_eq!(kind("s"), KIND_GHOST);
    assert_eq!(kind("p"), KIND_GHOST);
    assert_eq!(kind("ax"), KIND_AXIOM);
    assert_eq!(kind("u"), KIND_UNINTERP);
    assert_eq!(kind("wrapper"), KIND_EXT_BODY_SPEC);
    assert_eq!(kind("bare"), KIND_EXT_BODY_BARE);
    assert_eq!(kind("spins"), KIND_EXEC_PARTIAL);
    assert_eq!(kind("Opaque"), KIND_OPAQUE_TYPE);
    assert_eq!(kind("ExT"), KIND_EXT_TYPE);
    assert_eq!(kind("<TasClone>::clone"), KIND_ASSUME_SPEC);
    assert_eq!(kind("Holder::get"), KIND_EXEC);
    assert_eq!(kind("Thing::clone"), KIND_EXEC);
    assert_eq!(kind("Tr::default_m"), KIND_EXEC);
    assert_eq!(kind("plain::assume"), KIND_ASSUME_CALL);
    assert_eq!(kind("p::assume"), KIND_ASSUME_CALL);
    assert!(
        !names(&s)
            .iter()
            .any(|n| n == "Normal" || n == "Tr::decl" || n == "test_only")
    );
}

#[test]
fn kani_assume_is_not_a_verus_assumption() {
    let (s, _) = scan_one(
        CORE,
        &[(
            "crates/bc_core/src/lib.rs",
            "verus! { fn f() { kani::assume(true); } }",
        )],
    );
    assert_eq!(names(&s), ["f"]);
}

#[test]
fn macros_that_verus_reads_are_scanned() {
    let (s, _) = scan_one(
        CORE,
        &[(
            "crates/bc_core/src/lib.rs",
            r#"
macro_rules! dual_verified { ($($t:tt)*) => {} }
macro_rules! helper { () => { if true {} } }
dual_verified! {
    /// A kernel.
    pub fn k(x: u8) -> (r: u8)
        requires [ x < 3 ]
        ensures [ r == x ]
    {
        x
    }
}
exec_spec_verified! {
    pub open spec fn sp(x: u8) -> u8 { x }
}
"#,
        )],
    );
    assert_eq!(item(&s, "dual_verified").kind, KIND_MACRO);
    assert_eq!(item(&s, "helper").kind, KIND_OUTSIDE);
    assert_eq!(item(&s, "k").kind, KIND_EXEC);
    assert_eq!(item(&s, "sp").kind, KIND_GHOST);
}

#[test]
fn functions_outside_verus_are_found_in_impls_and_trait_defaults() {
    let (s, _) = scan_one(
        CORE,
        &[(
            "crates/bc_core/src/lib.rs",
            r#"
pub struct A;
impl A { pub fn m(&self) {} }
impl core::fmt::Display for A { fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result { Ok(()) } }
pub trait W { fn required(&self); fn provided(&self) {} }
extern "C" { fn declared(); }
"#,
        )],
    );
    assert_eq!(names(&s), ["A::m", "A::fmt", "W::provided"]);
    assert!(s.items.iter().all(|i| i.kind == KIND_OUTSIDE));
}

#[test]
fn modules_are_followed_to_their_files() {
    let (s, _) = scan_one(
        CORE,
        &[
            (
                "crates/bc_core/src/lib.rs",
                "mod a; mod b; mod inline { mod deep; }",
            ),
            ("crates/bc_core/src/a.rs", "pub fn in_a() {} mod c;"),
            ("crates/bc_core/src/a/c.rs", "pub fn in_c() {}"),
            (
                "crates/bc_core/src/b/mod.rs",
                "pub fn in_b() {} #[path = \"../other.rs\"] mod elsewhere;",
            ),
            ("crates/bc_core/src/other.rs", "pub fn in_other() {}"),
            ("crates/bc_core/src/inline/deep.rs", "pub fn in_deep() {}"),
        ],
    );
    assert!(s.errors.is_empty(), "{:?}", s.errors);
    let mut n = names(&s);
    n.sort();
    assert_eq!(
        n,
        [
            "a::c::in_c",
            "a::in_a",
            "b::elsewhere::in_other",
            "b::in_b",
            "inline::deep::in_deep"
        ]
    );
    assert_eq!(item(&s, "a::c::in_c").file, "crates/bc_core/src/a/c.rs");
}

#[test]
fn missing_and_unparsable_files_are_errors() {
    let (s, _) = scan_one(
        CORE,
        &[
            ("crates/bc_core/src/lib.rs", "mod gone; mod broken;"),
            ("crates/bc_core/src/broken.rs", "fn ("),
        ],
    );
    assert_eq!(s.errors.len(), 2, "{:?}", s.errors);
}

#[test]
fn tags_are_read_above_the_item_or_before_its_fn_keyword() {
    let lines = [
        "// coverage: miri(t1); why: io", // 1
        "/// Doc.",                       // 2
        "#[inline]",                      // 3
        "pub fn a() {}",                  // 4
        "",                               // 5
        "/// Doc.",                       // 6
        "// coverage: kani(h); why: ffi", // 7
        "pub fn b() {}",                  // 8
        "",                               // 9
        "// unrelated",                   // 10
        "pub fn c() {}",                  // 11
        "// coverage: miri(x)",           // 12
        "// coverage: miri(y)",           // 13
        "pub fn d() {}",                  // 14
    ];
    let a = find_tag(&lines, 2, 4);
    assert_eq!(
        a,
        Tag {
            kind: TAG_MIRI,
            targets: vec!["t1".into()],
            why: vec!["io".into()]
        }
    );
    assert_eq!(find_tag(&lines, 6, 8).kind, TAG_KANI);
    assert_eq!(find_tag(&lines, 11, 11).kind, TAG_NONE);
    assert_eq!(find_tag(&lines, 14, 14).kind, TAG_MALFORMED);
}

#[test]
fn tags_are_parsed_strictly() {
    assert_eq!(
        parse_tag(" miri(a, via b); why: io, fmt"),
        Tag {
            kind: TAG_MIRI,
            targets: vec!["a".into(), "via b".into()],
            why: vec!["io".into(), "fmt".into()]
        }
    );
    assert_eq!(parse_tag(" shim(scripts/x.sh)").kind, TAG_SHIM);
    for bad in [
        " miri()",
        " miri(a",
        " verus(a)",
        " miri(a); because: io",
        " miri(a); why: io; x",
        " kani",
    ] {
        assert_eq!(parse_tag(bad).kind, TAG_MALFORMED, "{bad}");
    }
    assert!(why_ok(&parse_tag(" miri(a); why: io, hw")));
    assert!(!why_ok(&parse_tag(" miri(a); why: io, laziness")));
    assert!(!why_ok(&parse_tag(" miri(a)")));
}

#[test]
fn branches_are_found_anywhere_in_a_body() {
    let free = |code: &str| branch_free(&code.parse::<TokenStream>().unwrap_or_default());
    assert!(free("{ let x = f(a, &b); g(x) }"));
    assert!(!free("{ let r = &&x; }"));
    for code in [
        "{ if a { } }",
        "{ match a { _ => () } }",
        "{ while a {} }",
        "{ for x in y {} }",
        "{ loop {} }",
        "{ f()?; }",
        "{ a && b }",
        "{ a || b }",
        "{ x.unwrap() }",
        "{ x.unwrap_or(0) }",
        "{ x.expect(\"m\") }",
        "{ g(|| { if a {} }) }",
    ] {
        assert!(!free(code), "{code}");
    }
}

#[test]
fn targets_must_exist_and_mention_the_function() {
    let (s, _) = scan_one(
        CORE,
        &[
            (
                "crates/bc_core/src/lib.rs",
                r#"
// coverage: miri(t_calls); why: io
pub fn direct() {}
// coverage: miri(t_other); why: io
pub fn not_mentioned() {}
// coverage: miri(t_missing); why: io
pub fn missing_test() {}
// coverage: miri(t_caller); why: io
pub fn caller() { helper(); }
// coverage: miri(via caller); why: io
fn helper() {}
// coverage: miri(via direct); why: io
fn not_called_by_direct() {}
// coverage: kani(h); why: ffi
pub fn checked() {}
// coverage: kani(t_calls); why: ffi
pub fn kani_tag_naming_a_test() {}
// coverage: shim(scripts/it.sh); why: hw
pub fn entry() {}
// coverage: shim(scripts/none.sh); why: hw
pub fn entry_missing() {}
#[cfg(test)]
mod tests {
    #[test] fn t_calls() { super::direct(); super::kani_tag_naming_a_test(); }
    #[test] fn t_other() { }
    #[test] fn t_caller() { super::caller(); }
}
#[cfg(kani)]
mod proofs { #[kani::proof] fn h() { super::checked(); } }
"#,
            ),
            ("scripts/it.sh", ""),
        ],
    );
    let ok = |n: &str| item(&s, n).targets_ok;
    assert!(ok("direct"));
    assert!(!ok("not_mentioned"));
    assert!(!ok("missing_test"));
    assert!(ok("caller"));
    assert!(ok("helper"));
    assert!(!ok("not_called_by_direct"));
    assert!(ok("checked"));
    assert!(!ok("kani_tag_naming_a_test"));
    assert!(ok("entry"));
    assert!(!ok("entry_missing"));
}

#[test]
fn facts_carry_the_file_name_role_and_checks() {
    let (s, _) = scan_one(
        CORE,
        &[
            ("crates/bc_core/src/lib.rs", "mod unverified_glue;"),
            (
                "crates/bc_core/src/unverified_glue.rs",
                "// coverage: shim(scripts/it.sh); why: hw\npub fn e() { if x {} }",
            ),
            ("scripts/it.sh", ""),
        ],
    );
    let f = facts(&s);
    assert_eq!(f.len(), 1);
    assert_eq!(f[0].file, b"unverified_glue.rs");
    assert_eq!(f[0].role, ROLE_CORE);
    assert_eq!(
        (f[0].tag, f[0].why_ok, f[0].targets_ok, f[0].branch_free),
        (TAG_SHIM, true, true, false)
    );
}

#[test]
fn the_lists_of_crates_and_miri_packages_are_checked_against_the_repository() {
    let good_toml =
        "members = [\n    \"crates/bc_core\",\n]\nexclude = [\n    \"examples/m5stamp_c3\",\n]\n";
    let script = CRATES
        .iter()
        .filter(|c| c.miri)
        .map(|c| format!("--package {}\n", c.name))
        .collect::<String>();
    assert!(
        check_lists(&Mem::new(&[
            ("Cargo.toml", good_toml),
            ("scripts/run_miri_tests.sh", &script)
        ]))
        .is_empty()
    );
    let new_member = "members = [\n    \"crates/bc_new\",\n]\n";
    assert_eq!(
        check_lists(&Mem::new(&[
            ("Cargo.toml", new_member),
            ("scripts/run_miri_tests.sh", &script)
        ]))
        .len(),
        1
    );
    assert_eq!(
        check_lists(&Mem::new(&[
            ("Cargo.toml", good_toml),
            ("scripts/run_miri_tests.sh", "")
        ]))
        .len(),
        4
    );
    assert_eq!(check_lists(&Mem::new(&[])).len(), 2);
}
