#![warn(clippy::all)]
//! Library for Metropolis: a dynamic multi-modal traffic-assignment simulator.

pub mod agent;
pub mod convergence;
pub mod event;
pub mod learning;
pub mod mode;
pub mod mode_utility;
pub mod network;
pub mod schedule_utility;
pub mod simulation;
pub mod units;

#[global_allocator]
static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

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
