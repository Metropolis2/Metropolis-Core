// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Library for Metropolis: a dynamic multi-modal traffic-assignment simulator.
#![warn(
    elided_lifetimes_in_paths,
    explicit_outlives_requirements,
    macro_use_extern_crate,
    missing_debug_implementations,
    missing_docs,
    non_ascii_idents,
    noop_method_call,
    trivial_numeric_casts,
    trivial_casts,
    unreachable_pub,
    unused_crate_dependencies,
    unused_extern_crates,
    unused_import_braces,
    unused_lifetimes,
    unused_qualifications
)]
#![warn(clippy::all)]
#![doc(html_no_source)]

pub mod agent;
pub mod event;
pub mod learning;
pub mod mode;
pub mod network;
pub mod parameters;
pub mod report;
pub mod schedule_utility;
mod schema;
mod serialization;
pub mod simulation;
pub mod stop;
pub mod travel_utility;
pub mod units;

#[cfg(all(feature = "jemalloc", not(target_env = "msvc")))]
#[global_allocator]
static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

#[cfg(all(feature = "jemalloc", not(target_env = "msvc")))]
/// Displays statistics on allocated and resident memory.
pub fn show_stats() {
    jemalloc_ctl::epoch::advance().unwrap();

    let allocated = jemalloc_ctl::stats::allocated::read().unwrap();
    let resident = jemalloc_ctl::stats::resident::read().unwrap();
    log::debug!(
        "{} bytes allocated/{} bytes resident",
        indicatif::HumanBytes(allocated as u64).to_string(),
        indicatif::HumanBytes(resident as u64).to_string()
    );
}

#[cfg(any(not(feature = "jemalloc"), target_env = "msvc"))]
/// Displays statistics on allocated and resident memory.
pub fn show_stats() {}

// Re-exports.
// Dependencies only used in the bins.
use clap as _;
pub use report::write_report;
use simplelog as _;
