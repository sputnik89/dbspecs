//! Reusable proofs over SpecLib's existing definitions.
//!
//! Specs live in `crate::functional` and `crate::consistency`; this module
//! imports their semantics instead of defining another KV or history model.

pub mod consistency;
pub mod functional;
pub mod history;
