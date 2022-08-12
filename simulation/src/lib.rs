#![warn(clippy::all)]
#![feature(result_into_ok_or_err)]
//! Library for Metropolis: a dynamic multi-modal traffic-assignment simulator.

pub mod agent;
pub mod event;
pub mod learning;
pub mod mode;
pub mod network;
pub mod schedule_utility;
mod schema;
mod serialization;
pub mod simulation;
pub mod stop;
pub mod travel_utility;
pub mod units;

#[global_allocator]
static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

/// Display statistics on allocated and resident memory.
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
