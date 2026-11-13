// SPDX-License-Identifier: MIT

//! The parser's public entry points, used by tests only (the driver calls the verified
//! `parse_unit_ref`). Not verified: they call the verified functions without their
//! preconditions, which hold for a parser built here but are not stated to callers.

use alloc::vec::Vec;

use super::{DEFAULT_MAX_DEPTH, Parser};
use crate::error::BcError;
use crate::parser::{ExtensionPolicy, Lexer};
#[cfg(not(verus_keep_ghost))]
use verus_builtin::Ghost;
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl Parser {
    /// Creates a new Parser from the Lexer, returning Err on initial lexical error.
    // coverage: miri(test_fallible_parser_and_lexer); why: boundary
    pub fn try_new(mut lexer: Lexer) -> Result<Self, BcError> {
        let current_token = lexer.try_get_next_token()?;
        Ok(Self {
            lexer,
            current_token,
            loop_depth: 0,
            in_function: false,
            extension_policy: ExtensionPolicy::Allow,
            extension_uses: Vec::new(),
            depth: 0,
            last_line: 1,
            max_depth: DEFAULT_MAX_DEPTH,
            nodes: Vec::new(),
        })
    }
}

verus! {

impl Parser {
    /// Parses the program fully, returning Err on lexical/syntax error or `"quit"`: the indices
    /// of its statements in the arena [`Parser::take_code`]. The proved theorem is that of
    /// `parse_program_ref` (connected to the specification in `run_unit`).
    #[verifier::external_body]
    // coverage: miri(parse_program_returns_the_statements_in_the_arena); why: boundary
    pub fn try_parse_program(&mut self) -> Result<Vec<usize>, BcError> {
        self.parse_program_ref(Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary())).0
    }
}

} // verus!
