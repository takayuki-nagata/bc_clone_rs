// SPDX-License-Identifier: MIT

//! Reads the sources of the crates and reduces every item to the facts that `rules.rs` decides
//! on. This layer is a verification tool, checked by the tests below, not by Verus.
//!
//! What it reads:
//!
//! - the module tree of each crate, from its roots, following `mod` declarations (and `#[path]`);
//! - each item's `cfg`, evaluated in four builds: production (no `cfg` set), the tests under Miri
//!   (`test`, `miri`), Kani (`kani`) and Verus (`verus_keep_ghost`). Any other predicate (a
//!   feature, a target) is unknown and taken as possibly true, so an item is production code
//!   unless its `cfg` is false in the production build;
//! - outside `verus!`: functions, methods, default methods of traits, `macro_rules!`, `#[test]`
//!   functions and `#[kani::proof]` harnesses;
//! - inside `verus!`, `exec_spec_verified!` and `dual_verified!`: the token stream, item by item
//!   (attributes, modes, `requires`/`ensures`, `impl` blocks, opaque and bridged types,
//!   `assume_specification`, calls of `assume` and `admit`);
//! - the `// coverage:` comment of an item: in the comment lines just above it, or between its
//!   first line and its `fn` keyword.

use crate::rules::*;
use proc_macro2::{Delimiter, Spacing, TokenStream, TokenTree};
use quote::ToTokens;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use syn::punctuated::Punctuated;
use syn::{Meta, Token};

/// A crate root: a file and the module path its items get.
pub struct Root {
    pub file: &'static str,
    pub label: &'static str,
}

/// A crate the inventory covers.
pub struct CrateSpec {
    /// Package name.
    pub name: &'static str,
    /// Directory, relative to the repository root.
    pub dir: &'static str,
    pub roots: &'static [Root],
    /// `ROLE_*`.
    pub role: u8,
    /// Whether `scripts/run_miri_tests.sh` runs the unit tests of this package.
    pub miri: bool,
}

const fn root(file: &'static str, label: &'static str) -> Root {
    Root { file, label }
}

/// Every crate of the workspace and the examples.
pub const CRATES: &[CrateSpec] = &[
    CrateSpec {
        name: "bc_core",
        dir: "crates/bc_core",
        roots: &[root("src/lib.rs", "")],
        role: ROLE_CORE,
        miri: true,
    },
    CrateSpec {
        name: "bc_clone",
        dir: "crates/bc_cli",
        roots: &[root("src/main.rs", "")],
        role: ROLE_PRODUCT,
        miri: true,
    },
    CrateSpec {
        name: "bc_c_api",
        dir: "crates/bc_c_api",
        roots: &[root("src/lib.rs", "")],
        role: ROLE_PRODUCT,
        miri: true,
    },
    CrateSpec {
        name: "bc_zephyr",
        dir: "crates/bc_zephyr",
        roots: &[root("src/lib.rs", "")],
        role: ROLE_PRODUCT,
        miri: true,
    },
    CrateSpec {
        name: "bc_qemu_riscv32",
        dir: "crates/bc_qemu_riscv32",
        roots: &[root("src/main.rs", "")],
        role: ROLE_PRODUCT,
        miri: false,
    },
    CrateSpec {
        name: "bc_build_info",
        dir: "crates/bc_build_info",
        roots: &[root("src/lib.rs", ""), root("build.rs", "build")],
        role: ROLE_PRODUCT,
        miri: false,
    },
    CrateSpec {
        name: "m5stamp_c3_bc",
        dir: "examples/m5stamp_c3",
        roots: &[root("src/lib.rs", ""), root("src/bin/main.rs", "main")],
        role: ROLE_PRODUCT,
        miri: false,
    },
    CrateSpec {
        name: "bc_wasm",
        dir: "examples/wasm_web_app/crate",
        roots: &[root("src/lib.rs", "")],
        role: ROLE_PRODUCT,
        miri: false,
    },
    CrateSpec {
        name: "bc_spec",
        dir: "crates/bc_spec",
        roots: &[root("src/lib.rs", ""), root("src/main.rs", "main")],
        role: ROLE_SPEC,
        miri: false,
    },
    CrateSpec {
        name: "bc_inventory",
        dir: "crates/bc_inventory",
        roots: &[root("src/lib.rs", ""), root("src/main.rs", "main")],
        role: ROLE_TOOL,
        miri: false,
    },
];

/// The reasons a function cannot be covered by a higher tier.
///
/// `boundary` is a public entry point of `bc_core` whose precondition (an invariant of a type
/// whose fields are private to the crate) its unverified callers cannot state, so it calls the
/// verified function with that precondition without proof (`AGENTS.md` argues each one).
/// `trait` is an implementation of a standard trait whose vstd specification does not fit it.
pub const WHY_WORDS: &[&str] = &[
    "dyn", "fmt", "string", "ffi", "io", "signal", "hw", "bindgen", "build", "boundary", "trait",
];

/// Reads the files of the repository (or of a test fixture).
pub trait Source {
    /// The text of `path`, relative to the repository root.
    fn read(&self, path: &Path) -> Option<String>;
    /// Whether `path` exists.
    fn exists(&self, path: &Path) -> bool;
}

/// The files under a directory.
pub struct FsSource(pub PathBuf);

impl Source for FsSource {
    fn read(&self, path: &Path) -> Option<String> {
        std::fs::read_to_string(self.0.join(path)).ok()
    }
    fn exists(&self, path: &Path) -> bool {
        self.0.join(path).exists()
    }
}

/// A parsed `// coverage:` tag.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Tag {
    /// `TAG_*`.
    pub kind: u8,
    /// The harnesses, tests (`via <caller>` for a caller) or integration tests.
    pub targets: Vec<String>,
    /// The reasons.
    pub why: Vec<String>,
}

/// One item: a function, an assumption or a call of `assume`.
#[derive(Clone, Debug)]
pub struct Item {
    /// Index in [`CRATES`].
    pub krate: usize,
    /// File, relative to the repository root.
    pub file: String,
    /// Path within the crate (`eval::Evaluator::new`).
    pub name: String,
    /// The function's own name, which a test or harness must mention.
    pub simple: String,
    /// For a method of a trait implementation (`Display::fmt`, `Clone::clone`), which is called
    /// through the trait: the implementing type, whose mention also counts.
    pub alt: Option<String>,
    /// `KIND_*`.
    pub kind: u8,
    pub tag: Tag,
    /// Identifiers in the body.
    pub body: BTreeSet<String>,
    /// The body has no branch (for shims).
    pub branch_free: bool,
    /// Line of the `fn` keyword (for messages).
    pub line: usize,
    /// Set by [`resolve`]: the tag's targets exist and cover the item.
    pub targets_ok: bool,
}

/// A test or harness.
#[derive(Clone, Debug)]
pub struct Check {
    pub krate: usize,
    pub name: String,
    pub body: BTreeSet<String>,
}

/// Everything read from the sources.
#[derive(Default, Debug)]
pub struct Scan {
    pub items: Vec<Item>,
    /// `#[test]` functions that the Miri run executes.
    pub miri_tests: Vec<Check>,
    /// `#[kani::proof]` harnesses.
    pub harnesses: Vec<Check>,
    /// Problems that prevent a reliable inventory (unreadable or missing files).
    pub errors: Vec<String>,
}

// --- cfg ---

/// A build in which `cfg` is evaluated.
#[derive(Clone, Copy)]
struct Build {
    test: bool,
    miri: bool,
    kani: bool,
    ghost: bool,
}

const PROD: Build = Build {
    test: false,
    miri: false,
    kani: false,
    ghost: false,
};
const TEST: Build = Build {
    test: true,
    miri: true,
    kani: false,
    ghost: false,
};
const KANI: Build = Build {
    test: false,
    miri: false,
    kani: true,
    ghost: false,
};
const GHOST: Build = Build {
    test: false,
    miri: false,
    kani: false,
    ghost: true,
};

/// In which builds an item may be compiled.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Active {
    pub prod: bool,
    pub test: bool,
    pub kani: bool,
    pub ghost: bool,
}

const ALL: Active = Active {
    prod: true,
    test: true,
    kani: true,
    ghost: true,
};

impl Active {
    fn and(self, o: Active) -> Active {
        Active {
            prod: self.prod && o.prod,
            test: self.test && o.test,
            kani: self.kani && o.kani,
            ghost: self.ghost && o.ghost,
        }
    }
}

/// The value of a `cfg` predicate: `None` if unknown.
fn eval_cfg(m: &Meta, b: Build) -> Option<bool> {
    match m {
        Meta::Path(p) => {
            let id = p.get_ident()?.to_string();
            match id.as_str() {
                "test" => Some(b.test),
                "miri" => Some(b.miri),
                "kani" => Some(b.kani),
                "verus_keep_ghost" => Some(b.ghost),
                "doc" | "verus_verify_core" => Some(false),
                _ => None,
            }
        }
        Meta::NameValue(_) => None,
        Meta::List(l) => {
            let args = l
                .parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated)
                .ok()?;
            let id = l.path.get_ident()?.to_string();
            let vals: Vec<Option<bool>> = args.iter().map(|a| eval_cfg(a, b)).collect();
            match id.as_str() {
                "not" => vals.first().copied().flatten().map(|v| !v),
                "all" => {
                    if vals.contains(&Some(false)) {
                        Some(false)
                    } else if vals.iter().all(|v| *v == Some(true)) {
                        Some(true)
                    } else {
                        None
                    }
                }
                "any" => {
                    if vals.contains(&Some(true)) {
                        Some(true)
                    } else if vals.iter().all(|v| *v == Some(false)) {
                        Some(false)
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
    }
}

/// The attributes of an item, as `Meta`s (an attribute that is not a `Meta` is dropped).
fn attr_metas(attrs: &[syn::Attribute]) -> Vec<Meta> {
    attrs.iter().map(|a| a.meta.clone()).collect()
}

/// The attributes in effect in build `b`: `cfg_attr(p, a, ...)` gives `a, ...` when `p` may hold.
fn effective(metas: &[Meta], b: Build) -> Vec<Meta> {
    let mut out = Vec::new();
    for m in metas {
        if let Meta::List(l) = m
            && l.path.is_ident("cfg_attr")
        {
            if let Ok(args) = l.parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated) {
                let mut it = args.into_iter();
                if let Some(pred) = it.next()
                    && eval_cfg(&pred, b) != Some(false)
                {
                    out.extend(effective(&it.collect::<Vec<_>>(), b));
                }
            }
        } else {
            out.push(m.clone());
        }
    }
    out
}

/// In which builds an item with these attributes may be compiled.
fn active(metas: &[Meta]) -> Active {
    let in_build = |b: Build| {
        effective(metas, b).iter().all(|m| match m {
            Meta::List(l) if l.path.is_ident("cfg") => l
                .parse_args::<Meta>()
                .map(|p| eval_cfg(&p, b) != Some(false))
                .unwrap_or(true),
            _ => true,
        })
    };
    Active {
        prod: in_build(PROD),
        test: in_build(TEST),
        kani: in_build(KANI),
        ghost: in_build(GHOST),
    }
}

/// The path of a `Meta`, as `a::b`.
fn meta_path(m: &Meta) -> String {
    m.path()
        .segments
        .iter()
        .map(|s| s.ident.to_string())
        .collect::<Vec<_>>()
        .join("::")
}

/// Whether the attributes in build `b` include `path` (`verifier::external_body`, or the old
/// form `verifier(external_body)`).
fn has_attr(metas: &[Meta], b: Build, path: &str) -> bool {
    effective(metas, b).iter().any(|m| {
        let p = meta_path(m);
        if p == path {
            return true;
        }
        if let (Some(rest), Meta::List(l)) = (path.strip_prefix("verifier::"), m)
            && p == "verifier"
        {
            return l
                .tokens
                .to_string()
                .split(|c: char| !c.is_alphanumeric() && c != '_')
                .any(|w| w == rest);
        }
        false
    })
}

// --- tokens ---

/// The identifiers in a token stream.
fn idents(ts: &TokenStream, out: &mut BTreeSet<String>) {
    for t in ts.clone() {
        match t {
            TokenTree::Ident(i) => {
                let s = i.to_string();
                out.insert(s.strip_prefix("r#").map(str::to_string).unwrap_or(s));
            }
            TokenTree::Group(g) => idents(&g.stream(), out),
            _ => {}
        }
    }
}

/// Whether a body has no branch: no `if`, `match`, loop, `?`, `&&`, `||`, `unwrap*` or `expect*`.
pub fn branch_free(ts: &TokenStream) -> bool {
    let toks: Vec<TokenTree> = ts.clone().into_iter().collect();
    for (k, t) in toks.iter().enumerate() {
        match t {
            TokenTree::Ident(i) => {
                let s = i.to_string();
                if matches!(s.as_str(), "if" | "match" | "while" | "for" | "loop")
                    || s.starts_with("unwrap")
                    || s.starts_with("expect")
                {
                    return false;
                }
            }
            TokenTree::Punct(p) => {
                let c = p.as_char();
                if c == '?' {
                    return false;
                }
                if (c == '&' || c == '|')
                    && p.spacing() == Spacing::Joint
                    && matches!(toks.get(k + 1), Some(TokenTree::Punct(q)) if q.as_char() == c)
                {
                    return false;
                }
            }
            TokenTree::Group(g) => {
                if !branch_free(&g.stream()) {
                    return false;
                }
            }
            TokenTree::Literal(_) => {}
        }
    }
    true
}

/// The calls of `assume` and `admit` in a token stream (not `kani::assume`).
fn assume_calls(ts: &TokenStream) -> usize {
    let toks: Vec<TokenTree> = ts.clone().into_iter().collect();
    let mut n = 0;
    for (k, t) in toks.iter().enumerate() {
        match t {
            TokenTree::Ident(i) if i == "assume" || i == "admit" => {
                let call = matches!(toks.get(k + 1), Some(TokenTree::Group(g)) if g.delimiter() == Delimiter::Parenthesis);
                let qualified =
                    k > 0 && matches!(&toks[k - 1], TokenTree::Punct(p) if p.as_char() == ':');
                if call && !qualified {
                    n += 1;
                }
            }
            TokenTree::Group(g) => n += assume_calls(&g.stream()),
            _ => {}
        }
    }
    n
}

// --- tags ---

/// Reads the `// coverage:` tag of an item whose first line is `first` and whose `fn` keyword is
/// on line `kw` (1-based).
pub fn find_tag(lines: &[&str], first: usize, kw: usize) -> Tag {
    let mut found: Vec<&str> = Vec::new();
    let mut l = first;
    while l > 1 {
        let t = lines.get(l - 2).map(|s| s.trim()).unwrap_or("");
        if t.starts_with("//") {
            if let Some(rest) = t.strip_prefix("// coverage:") {
                found.push(rest);
            }
            l -= 1;
        } else {
            break;
        }
    }
    for ln in first..=kw.max(first) {
        if let Some(rest) = lines
            .get(ln.wrapping_sub(1))
            .map(|s| s.trim())
            .and_then(|t| t.strip_prefix("// coverage:"))
        {
            found.push(rest);
        }
    }
    match found.as_slice() {
        [] => Tag {
            kind: TAG_NONE,
            ..Tag::default()
        },
        [one] => parse_tag(one),
        _ => Tag {
            kind: TAG_MALFORMED,
            ..Tag::default()
        },
    }
}

/// Parses the text after `// coverage:`: `tier(target, ...)` and an optional `; why: word, ...`.
pub fn parse_tag(text: &str) -> Tag {
    let bad = Tag {
        kind: TAG_MALFORMED,
        ..Tag::default()
    };
    let mut parts = text.split(';');
    let head = parts.next().unwrap_or("").trim();
    let Some((tier, rest)) = head.split_once('(') else {
        return bad;
    };
    let Some(args) = rest.strip_suffix(')') else {
        return bad;
    };
    let kind = match tier.trim() {
        "kani" => TAG_KANI,
        "miri" => TAG_MIRI,
        "shim" => TAG_SHIM,
        _ => return bad,
    };
    let targets: Vec<String> = args
        .split(',')
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .collect();
    if targets.is_empty() {
        return bad;
    }
    let mut why = Vec::new();
    match (parts.next(), parts.next()) {
        (None, _) => {}
        (Some(w), None) => {
            let Some(words) = w.trim().strip_prefix("why:") else {
                return bad;
            };
            why = words
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();
        }
        _ => return bad,
    }
    Tag { kind, targets, why }
}

/// The tag gives reasons, all from [`WHY_WORDS`].
pub fn why_ok(tag: &Tag) -> bool {
    !tag.why.is_empty() && tag.why.iter().all(|w| WHY_WORDS.contains(&w.as_str()))
}

// --- the walk ---

struct Ctx<'a> {
    krate: usize,
    file: String,
    lines: Vec<&'a str>,
    /// Module path within the crate.
    modpath: Vec<String>,
    /// Directory of the files of child modules.
    child_dir: PathBuf,
    act: Active,
    /// The implementing type, inside a trait implementation.
    trait_ty: Option<String>,
}

impl Ctx<'_> {
    fn qualify(&self, ty: Option<&str>, name: &str) -> String {
        let mut p = self.modpath.clone();
        if let Some(t) = ty {
            p.push(t.to_string());
        }
        p.push(name.to_string());
        p.join("::")
    }
}

fn line_of(t: &TokenTree) -> usize {
    t.span().start().line
}

/// Scans every crate of [`CRATES`].
pub fn scan_all(src: &dyn Source) -> Scan {
    let mut scan = Scan::default();
    for k in 0..CRATES.len() {
        scan_crate(src, k, &mut scan);
    }
    scan
}

/// Scans one crate.
pub fn scan_crate(src: &dyn Source, krate: usize, scan: &mut Scan) {
    let spec = &CRATES[krate];
    for r in spec.roots {
        let file = Path::new(spec.dir).join(r.file);
        let child_dir = file.parent().map(Path::to_path_buf).unwrap_or_default();
        let modpath = if r.label.is_empty() {
            vec![]
        } else {
            vec![r.label.to_string()]
        };
        scan_file(src, krate, &file, modpath, child_dir, ALL, scan);
    }
}

fn scan_file(
    src: &dyn Source,
    krate: usize,
    file: &Path,
    modpath: Vec<String>,
    child_dir: PathBuf,
    act: Active,
    scan: &mut Scan,
) {
    let Some(text) = src.read(file) else {
        scan.errors.push(format!("cannot read {}", file.display()));
        return;
    };
    let parsed = match syn::parse_file(&text) {
        Ok(f) => f,
        Err(e) => {
            scan.errors
                .push(format!("cannot parse {}: {e}", file.display()));
            return;
        }
    };
    let mut ctx = Ctx {
        krate,
        file: file.to_string_lossy().into_owned(),
        lines: text.lines().collect(),
        modpath,
        child_dir,
        act,
        trait_ty: None,
    };
    scan_items(src, &parsed.items, &mut ctx, scan);
}

fn first_line(attrs: &[syn::Attribute], fallback: usize) -> usize {
    attrs
        .first()
        .map(|a| a.pound_token.span.start().line)
        .unwrap_or(fallback)
        .min(fallback)
}

fn scan_items(src: &dyn Source, items: &[syn::Item], ctx: &mut Ctx, scan: &mut Scan) {
    for item in items {
        match item {
            syn::Item::Fn(f) => {
                let metas = attr_metas(&f.attrs);
                let act = ctx.act.and(active(&metas));
                let kw = f.sig.fn_token.span.start().line;
                outside_fn(
                    ctx,
                    scan,
                    &metas,
                    act,
                    None,
                    &f.sig.ident.to_string(),
                    &f.block.to_token_stream(),
                    first_line(&f.attrs, kw),
                    kw,
                );
            }
            syn::Item::Impl(i) => {
                let act = ctx.act.and(active(&attr_metas(&i.attrs)));
                let ty = type_name(&i.self_ty);
                let saved =
                    std::mem::replace(&mut ctx.trait_ty, i.trait_.as_ref().map(|_| ty.clone()));
                for it in &i.items {
                    if let syn::ImplItem::Fn(m) = it {
                        let metas = attr_metas(&m.attrs);
                        let kw = m.sig.fn_token.span.start().line;
                        outside_fn(
                            ctx,
                            scan,
                            &metas,
                            act.and(active(&metas)),
                            Some(&ty),
                            &m.sig.ident.to_string(),
                            &m.block.to_token_stream(),
                            first_line(&m.attrs, kw),
                            kw,
                        );
                    }
                }
                ctx.trait_ty = saved;
            }
            syn::Item::Trait(t) => {
                let act = ctx.act.and(active(&attr_metas(&t.attrs)));
                let ty = t.ident.to_string();
                for it in &t.items {
                    if let syn::TraitItem::Fn(m) = it
                        && let Some(body) = &m.default
                    {
                        let metas = attr_metas(&m.attrs);
                        let kw = m.sig.fn_token.span.start().line;
                        outside_fn(
                            ctx,
                            scan,
                            &metas,
                            act.and(active(&metas)),
                            Some(&ty),
                            &m.sig.ident.to_string(),
                            &body.to_token_stream(),
                            first_line(&m.attrs, kw),
                            kw,
                        );
                    }
                }
            }
            syn::Item::Mod(m) => {
                let metas = attr_metas(&m.attrs);
                let act = ctx.act.and(active(&metas));
                let name = m.ident.to_string();
                let mut modpath = ctx.modpath.clone();
                modpath.push(name.clone());
                if let Some((_, items)) = &m.content {
                    let saved = (
                        std::mem::replace(&mut ctx.modpath, modpath),
                        ctx.child_dir.clone(),
                        ctx.act,
                    );
                    ctx.child_dir = ctx.child_dir.join(&name);
                    ctx.act = act;
                    scan_items(src, items, ctx, scan);
                    ctx.modpath = saved.0;
                    ctx.child_dir = saved.1;
                    ctx.act = saved.2;
                } else {
                    let explicit = metas.iter().find_map(|m| match m {
                        Meta::NameValue(nv) if nv.path.is_ident("path") => match &nv.value {
                            syn::Expr::Lit(syn::ExprLit {
                                lit: syn::Lit::Str(s),
                                ..
                            }) => Some(s.value()),
                            _ => None,
                        },
                        _ => None,
                    });
                    let candidates: Vec<PathBuf> = match &explicit {
                        Some(p) => vec![normalize(
                            &Path::new(&ctx.file)
                                .parent()
                                .unwrap_or(Path::new(""))
                                .join(p),
                        )],
                        None => vec![
                            ctx.child_dir.join(format!("{name}.rs")),
                            ctx.child_dir.join(&name).join("mod.rs"),
                        ],
                    };
                    match candidates.iter().find(|c| src.exists(c)) {
                        Some(f) => {
                            let child_dir = if f.file_name().is_some_and(|n| n == "mod.rs")
                                || explicit.is_some()
                            {
                                f.parent().map(Path::to_path_buf).unwrap_or_default()
                            } else {
                                ctx.child_dir.join(&name)
                            };
                            scan_file(src, ctx.krate, f, modpath, child_dir, act, scan);
                        }
                        None => scan
                            .errors
                            .push(format!("{}: module `{name}` not found", ctx.file)),
                    }
                }
            }
            syn::Item::Macro(m) => {
                let act = ctx.act.and(active(&attr_metas(&m.attrs)));
                let name = m
                    .mac
                    .path
                    .segments
                    .last()
                    .map(|s| s.ident.to_string())
                    .unwrap_or_default();
                match name.as_str() {
                    "verus" | "exec_spec_verified" | "dual_verified" => {
                        let saved = ctx.act;
                        ctx.act = act;
                        scan_verus(&m.mac.tokens, ctx, scan, None);
                        ctx.act = saved;
                    }
                    // Property tests: `proptest! { #[test] fn name(x in s) { ... } }`.
                    "proptest" => macro_tests(ctx, scan, act, &m.mac.tokens),
                    // `dual_verified!` is trusted to expand the body Verus checked unchanged in a
                    // normal build. Any other macro is code, covered like a function.
                    "macro_rules" if act.prod || act.ghost => {
                        if let Some(id) = &m.ident {
                            let kw = m.mac.path.segments[0].ident.span().start().line;
                            let id = id.to_string();
                            let kind = if id == "dual_verified" {
                                KIND_MACRO
                            } else {
                                KIND_OUTSIDE
                            };
                            if kind == KIND_MACRO || act.prod {
                                push_item(
                                    ctx,
                                    scan,
                                    None,
                                    &id,
                                    kind,
                                    &m.mac.tokens,
                                    first_line(&m.attrs, kw),
                                    kw,
                                );
                            }
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
}

/// `a/b/../c` → `a/c`.
fn normalize(p: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for c in p.components() {
        match c {
            std::path::Component::ParentDir => {
                out.pop();
            }
            std::path::Component::CurDir => {}
            other => out.push(other),
        }
    }
    out
}

fn type_name(t: &syn::Type) -> String {
    match t {
        syn::Type::Path(p) => p
            .path
            .segments
            .last()
            .map(|s| s.ident.to_string())
            .unwrap_or_default(),
        syn::Type::Reference(r) => type_name(&r.elem),
        other => other.to_token_stream().to_string(),
    }
}

/// The `#[test]` functions in the tokens of a test macro such as `proptest!`.
fn macro_tests(ctx: &Ctx, scan: &mut Scan, act: Active, ts: &TokenStream) {
    let toks: Vec<TokenTree> = ts.clone().into_iter().collect();
    let mut i = 0;
    while i < toks.len() {
        let is_test_attr = matches!(&toks[i], TokenTree::Punct(p) if p.as_char() == '#')
            && matches!(toks.get(i + 1), Some(TokenTree::Group(g))
                if g.delimiter() == Delimiter::Bracket && g.stream().to_string() == "test");
        if !is_test_attr {
            i += 1;
            continue;
        }
        let mut metas: Vec<Meta> = Vec::new();
        let mut k = i;
        while let (Some(TokenTree::Punct(p)), Some(TokenTree::Group(g))) =
            (toks.get(k), toks.get(k + 1))
        {
            if p.as_char() != '#' {
                break;
            }
            if let Ok(m) = syn::parse2::<Meta>(g.stream()) {
                metas.push(m);
            }
            k += 2;
        }
        let name = match (toks.get(k), toks.get(k + 1)) {
            (Some(TokenTree::Ident(f)), Some(TokenTree::Ident(n))) if f == "fn" => n.to_string(),
            _ => {
                i = k.max(i + 1);
                continue;
            }
        };
        let body = toks[k + 2..].iter().find_map(|t| match t {
            TokenTree::Group(g) if g.delimiter() == Delimiter::Brace => Some(g.stream()),
            _ => None,
        });
        let act = act.and(active(&metas));
        if act.test && !has_attr(&metas, TEST, "ignore") && CRATES[ctx.krate].miri {
            let mut b = BTreeSet::new();
            idents(&body.unwrap_or_default(), &mut b);
            scan.miri_tests.push(Check {
                krate: ctx.krate,
                name,
                body: b,
            });
        }
        i = k + 2;
    }
}

/// A function outside `verus!`: a test, a harness, or production code.
#[allow(
    clippy::too_many_arguments,
    reason = "the parts of a function item, shared by three kinds of item"
)]
fn outside_fn(
    ctx: &Ctx,
    scan: &mut Scan,
    metas: &[Meta],
    act: Active,
    ty: Option<&str>,
    name: &str,
    body: &TokenStream,
    first: usize,
    kw: usize,
) {
    if has_attr(metas, TEST, "test") {
        let ignored = has_attr(metas, TEST, "ignore");
        if act.test && !ignored && CRATES[ctx.krate].miri {
            let mut b = BTreeSet::new();
            idents(body, &mut b);
            scan.miri_tests.push(Check {
                krate: ctx.krate,
                name: name.to_string(),
                body: b,
            });
        }
        return;
    }
    if has_attr(metas, KANI, "kani::proof") || has_attr(metas, KANI, "kani::proof_for_contract") {
        if act.kani {
            let mut b = BTreeSet::new();
            idents(body, &mut b);
            scan.harnesses.push(Check {
                krate: ctx.krate,
                name: name.to_string(),
                body: b,
            });
        }
        return;
    }
    if act.prod {
        push_item(ctx, scan, ty, name, KIND_OUTSIDE, body, first, kw);
    }
}

#[allow(clippy::too_many_arguments, reason = "the parts of an item")]
fn push_item(
    ctx: &Ctx,
    scan: &mut Scan,
    ty: Option<&str>,
    name: &str,
    kind: u8,
    body: &TokenStream,
    first: usize,
    kw: usize,
) {
    let mut b = BTreeSet::new();
    idents(body, &mut b);
    scan.items.push(Item {
        krate: ctx.krate,
        file: ctx.file.clone(),
        name: ctx.qualify(ty, name),
        simple: name.to_string(),
        alt: ctx.trait_ty.clone(),
        kind,
        tag: find_tag(&ctx.lines, first, kw),
        body: b,
        branch_free: branch_free(body),
        line: kw,
        targets_ok: false,
    });
}

/// The position after the generic parameters `<...>` at the start of an `impl` header (0 if none).
fn skip_generics(header: &[&TokenTree]) -> usize {
    if !matches!(header.first(), Some(TokenTree::Punct(p)) if p.as_char() == '<') {
        return 0;
    }
    let mut depth = 0i32;
    for (k, t) in header.iter().enumerate() {
        if let TokenTree::Punct(p) = t {
            match p.as_char() {
                '<' => depth += 1,
                '>' => {
                    depth -= 1;
                    if depth == 0 {
                        return k + 1;
                    }
                }
                _ => {}
            }
        }
    }
    header.len()
}

/// Whether the token at `k` starts a new item inside `verus!`.
fn item_start(toks: &[TokenTree], k: usize) -> bool {
    match toks.get(k) {
        None => true,
        Some(TokenTree::Punct(p)) => p.as_char() == '#',
        Some(TokenTree::Ident(i)) => matches!(
            i.to_string().as_str(),
            "pub"
                | "fn"
                | "spec"
                | "proof"
                | "exec"
                | "open"
                | "closed"
                | "axiom"
                | "uninterp"
                | "impl"
                | "struct"
                | "enum"
                | "union"
                | "const"
                | "static"
                | "use"
                | "mod"
                | "trait"
                | "type"
                | "broadcast"
                | "global"
                | "assume_specification"
                | "unsafe"
                | "extern"
                | "layout"
                | "macro_rules"
                | "tracked"
                | "ghost"
        ),
        _ => false,
    }
}

/// The end (exclusive) of an item that starts its body search at `k`, and its body: a top-level
/// `;` ends a bodyless item, and a brace group followed by the start of an item (or the end) is
/// the body.
fn item_end(toks: &[TokenTree], mut k: usize) -> (usize, Option<TokenStream>, bool) {
    let mut has_spec = false;
    while k < toks.len() {
        match &toks[k] {
            TokenTree::Punct(p) if p.as_char() == ';' => return (k + 1, None, has_spec),
            TokenTree::Ident(i) if i == "requires" || i == "ensures" => has_spec = true,
            TokenTree::Group(g) if g.delimiter() == Delimiter::Brace && item_start(toks, k + 1) => {
                return (k + 1, Some(g.stream()), has_spec);
            }
            _ => {}
        }
        k += 1;
    }
    (k, None, has_spec)
}

fn scan_verus(ts: &TokenStream, ctx: &mut Ctx, scan: &mut Scan, ty: Option<&str>) {
    let toks: Vec<TokenTree> = ts.clone().into_iter().collect();
    let mut i = 0;
    while i < toks.len() {
        let start = i;
        // Attributes.
        let mut metas: Vec<Meta> = Vec::new();
        while let Some(TokenTree::Punct(p)) = toks.get(i) {
            if p.as_char() != '#' {
                break;
            }
            let inner = matches!(toks.get(i + 1), Some(TokenTree::Punct(q)) if q.as_char() == '!');
            let g = if inner { i + 2 } else { i + 1 };
            if let Some(TokenTree::Group(grp)) = toks.get(g) {
                if !inner && let Ok(m) = syn::parse2::<Meta>(grp.stream()) {
                    metas.push(m);
                }
                i = g + 1;
            } else {
                i += 1;
                break;
            }
        }
        // Modifiers.
        let mut mods: BTreeSet<String> = BTreeSet::new();
        while let Some(TokenTree::Ident(id)) = toks.get(i) {
            let s = id.to_string();
            if !matches!(
                s.as_str(),
                "pub"
                    | "open"
                    | "closed"
                    | "spec"
                    | "proof"
                    | "exec"
                    | "axiom"
                    | "uninterp"
                    | "unsafe"
                    | "async"
                    | "extern"
                    | "broadcast"
                    | "tracked"
                    | "ghost"
                    | "default"
                    | "const"
            ) {
                break;
            }
            // `const` is a modifier only before `fn`.
            if s == "const" && !matches!(toks.get(i + 1), Some(TokenTree::Ident(n)) if n == "fn") {
                break;
            }
            mods.insert(s);
            i += 1;
            match toks.get(i) {
                Some(TokenTree::Group(g)) if g.delimiter() == Delimiter::Parenthesis => i += 1,
                Some(TokenTree::Literal(_)) => i += 1,
                _ => {}
            }
        }
        let act = ctx.act.and(active(&metas));
        let first = toks.get(start).map(line_of).unwrap_or(0);
        let Some(head) = toks.get(i) else { break };
        let head_s = match head {
            TokenTree::Ident(id) => id.to_string(),
            _ => {
                i += 1;
                continue;
            }
        };
        match head_s.as_str() {
            "fn" => {
                let kw = line_of(head);
                let name = match toks.get(i + 1) {
                    Some(TokenTree::Ident(n)) => n.to_string(),
                    _ => String::new(),
                };
                let (end, body, has_spec) = item_end(&toks, i + 2);
                i = end;
                if !(act.prod || act.ghost) {
                    continue;
                }
                let ext_body = has_attr(&metas, GHOST, "verifier::external_body");
                let kind = if mods.contains("axiom") {
                    KIND_AXIOM
                } else if mods.contains("uninterp") {
                    KIND_UNINTERP
                } else if mods.contains("spec") {
                    if ext_body { KIND_UNINTERP } else { KIND_GHOST }
                } else if mods.contains("proof") {
                    if ext_body { KIND_AXIOM } else { KIND_GHOST }
                } else if body.is_none() {
                    // A declaration (a trait method without a default body).
                    continue;
                } else if has_attr(&metas, GHOST, "verifier::external") {
                    KIND_OUTSIDE
                } else if has_attr(&metas, GHOST, "verifier::external_fn_specification") {
                    KIND_ASSUME_SPEC
                } else if ext_body {
                    if has_spec {
                        KIND_EXT_BODY_SPEC
                    } else {
                        KIND_EXT_BODY_BARE
                    }
                } else if has_attr(&metas, GHOST, "verifier::exec_allows_no_decreases_clause") {
                    KIND_EXEC_PARTIAL
                } else {
                    KIND_EXEC
                };
                let body = body.unwrap_or_default();
                push_item(ctx, scan, ty, &name, kind, &body, first, kw);
                for _ in 0..assume_calls(&body) {
                    push_item(
                        ctx,
                        scan,
                        ty,
                        &format!("{name}::assume"),
                        KIND_ASSUME_CALL,
                        &TokenStream::new(),
                        kw,
                        kw,
                    );
                    if let Some(last) = scan.items.last_mut() {
                        last.tag = Tag::default();
                    }
                }
            }
            "impl" | "trait" => {
                let mut k = i + 1;
                while k < toks.len()
                    && !matches!(&toks[k], TokenTree::Group(g) if g.delimiter() == Delimiter::Brace)
                {
                    k += 1;
                }
                let header: Vec<&TokenTree> = toks[i + 1..k.min(toks.len())].iter().collect();
                let after_for = header
                    .iter()
                    .position(|t| matches!(t, TokenTree::Ident(f) if f == "for"));
                let from = after_for
                    .map(|p| p + 1)
                    .unwrap_or_else(|| skip_generics(&header));
                let name = header[from..]
                    .iter()
                    .find_map(|t| match t {
                        TokenTree::Ident(n) if n != "dyn" && n != "mut" => Some(n.to_string()),
                        _ => None,
                    })
                    .unwrap_or_default();
                if let Some(TokenTree::Group(g)) = toks.get(k) {
                    let saved = (ctx.act, ctx.trait_ty.clone());
                    ctx.act = act;
                    ctx.trait_ty = after_for.map(|_| name.clone());
                    scan_verus(&g.stream(), ctx, scan, Some(&name));
                    (ctx.act, ctx.trait_ty) = saved;
                }
                i = k + 1;
            }
            "struct" | "enum" | "union" => {
                let kw = line_of(head);
                let name = match toks.get(i + 1) {
                    Some(TokenTree::Ident(n)) => n.to_string(),
                    _ => String::new(),
                };
                let (end, _, _) = item_end(&toks, i + 2);
                i = end;
                if !(act.prod || act.ghost) {
                    continue;
                }
                let kind = if has_attr(&metas, GHOST, "verifier::external_type_specification") {
                    KIND_EXT_TYPE
                } else if has_attr(&metas, GHOST, "verifier::external_body") {
                    KIND_OPAQUE_TYPE
                } else {
                    continue;
                };
                push_item(ctx, scan, ty, &name, kind, &TokenStream::new(), first, kw);
            }
            "assume_specification" => {
                let kw = line_of(head);
                let name = match toks.get(i + 1) {
                    Some(TokenTree::Group(g)) => g.stream().to_string().replace(' ', ""),
                    _ => String::new(),
                };
                let (end, _, _) = item_end(&toks, i + 1);
                i = end;
                if act.prod || act.ghost {
                    push_item(
                        ctx,
                        scan,
                        ty,
                        &name,
                        KIND_ASSUME_SPEC,
                        &TokenStream::new(),
                        first,
                        kw,
                    );
                }
            }
            "mod" => {
                let name = match toks.get(i + 1) {
                    Some(TokenTree::Ident(n)) => n.to_string(),
                    _ => String::new(),
                };
                let (end, body, _) = item_end(&toks, i + 2);
                i = end;
                match body {
                    Some(b) => {
                        let saved = (ctx.modpath.clone(), ctx.act);
                        ctx.modpath.push(name);
                        ctx.act = act;
                        scan_verus(&b, ctx, scan, None);
                        ctx.modpath = saved.0;
                        ctx.act = saved.1;
                    }
                    None => scan.errors.push(format!(
                        "{}: `mod {name};` inside verus! is not supported",
                        ctx.file
                    )),
                }
            }
            _ => {
                let (end, _, _) = item_end(&toks, i + 1);
                i = end.max(i + 1);
            }
        }
    }
}

// --- targets ---

/// Sets `targets_ok` of every item: each harness, test, caller or integration test its tag
/// names exists and covers it.
pub fn resolve(scan: &mut Scan, src: &dyn Source) {
    let named = |body: &BTreeSet<String>, it: &Item| {
        body.contains(&it.simple) || it.alt.as_ref().is_some_and(|a| body.contains(a))
    };
    let mentions = |checks: &[Check], name: &str, it: &Item| {
        checks
            .iter()
            .any(|c| c.krate == it.krate && c.name == name && named(&c.body, it))
    };
    // Direct targets first; `via` callers by fixpoint.
    let n = scan.items.len();
    let mut ok = vec![false; n];
    let mut changed = true;
    while changed {
        changed = false;
        for idx in 0..n {
            if ok[idx] {
                continue;
            }
            let it = &scan.items[idx];
            let good = !it.tag.targets.is_empty()
                && it.tag.targets.iter().all(|t| match it.tag.kind {
                    TAG_KANI => mentions(&scan.harnesses, t, it),
                    TAG_MIRI => match t.strip_prefix("via ") {
                        Some(caller) => (0..n).any(|c| {
                            let ci = &scan.items[c];
                            ok[c]
                                && ci.krate == it.krate
                                && ci.tag.kind == TAG_MIRI
                                && (ci.simple == caller.trim() || ci.name == caller.trim())
                                && named(&ci.body, it)
                        }),
                        None => mentions(&scan.miri_tests, t, it),
                    },
                    TAG_SHIM => src.exists(Path::new(t)),
                    _ => false,
                });
            if good {
                ok[idx] = true;
                changed = true;
            }
        }
    }
    for (it, o) in scan.items.iter_mut().zip(ok) {
        it.targets_ok = o;
    }
}

/// The facts that `rules.rs` decides on, one per item.
pub fn facts(scan: &Scan) -> Vec<Fact> {
    scan.items
        .iter()
        .map(|it| Fact {
            file: Path::new(&it.file)
                .file_name()
                .map(|n| n.to_string_lossy().into_owned())
                .unwrap_or_default()
                .into_bytes(),
            role: CRATES[it.krate].role,
            kind: it.kind,
            tag: it.tag.kind,
            why_ok: why_ok(&it.tag),
            targets_ok: it.targets_ok,
            branch_free: it.branch_free,
        })
        .collect()
}

/// Checks that the inventory's list of crates and Miri packages matches the repository: every
/// workspace member and example is in [`CRATES`], and `scripts/run_miri_tests.sh` tests every
/// crate marked `miri`.
pub fn check_lists(src: &dyn Source) -> Vec<String> {
    let mut errors = Vec::new();
    let known: BTreeSet<&str> = CRATES.iter().map(|c| c.dir).collect();
    if let Some(toml) = src.read(Path::new("Cargo.toml")) {
        for line in toml.lines() {
            let t = line.trim().trim_end_matches(',');
            if let Some(dir) = t.strip_prefix('"').and_then(|s| s.strip_suffix('"'))
                && (dir.starts_with("crates/") || dir.starts_with("examples/"))
                && !known.contains(dir)
            {
                errors.push(format!(
                    "{dir} is in Cargo.toml but not in the inventory's list of crates"
                ));
            }
        }
    } else {
        errors.push("cannot read Cargo.toml".to_string());
    }
    match src.read(Path::new("scripts/run_miri_tests.sh")) {
        Some(script) => {
            for c in CRATES.iter().filter(|c| c.miri) {
                if !script.contains(&format!("--package {}", c.name)) {
                    errors.push(format!(
                        "{} is marked as tested under Miri, but run_miri_tests.sh does not test it",
                        c.name
                    ));
                }
            }
        }
        None => errors.push("cannot read scripts/run_miri_tests.sh".to_string()),
    }
    errors
}

#[cfg(test)]
mod tests;
