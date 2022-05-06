#![warn(clippy::all)]
#![feature(is_sorted)]
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
