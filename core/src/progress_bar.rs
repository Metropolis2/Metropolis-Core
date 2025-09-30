// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Progress bar and spinner for the library.
use std::{
    borrow::Cow,
    sync::{Arc, Mutex},
    time::Duration,
};

use indicatif::{ProgressBar, ProgressStyle};
use log::{log_enabled, Level};

/// Progress bar are refreshed each UPDATE events.
const UPDATE: u64 = 5000;
/// Interval in milliseconds when spinners are automatically ticked.
const UPDATE_MS: Duration = Duration::from_millis(1000);

/// A progress bar.
#[derive(Debug, Clone)]
pub struct MetroProgressBar {
    bp: ProgressBar,
    current: Arc<Mutex<u64>>,
}

impl MetroProgressBar {
    /// Returns a [MetroProgressBar] of given length.
    pub fn new(length: usize) -> Self {
        let bp = if log_enabled!(Level::Info) {
            ProgressBar::new(length as u64)
        } else {
            ProgressBar::hidden()
        };
        bp.set_style(
            ProgressStyle::default_bar()
                .template("{bar:60} ETA: {eta}")
                .unwrap(),
        );
        MetroProgressBar {
            bp,
            current: Arc::new(Mutex::new(0)),
        }
    }

    /// Adds a message to the [MetroProgressBar].
    pub fn with_message(self, msg: impl Into<Cow<'static, str>>) -> Self {
        let bp = self.bp.with_message(msg);
        bp.set_style(
            ProgressStyle::default_bar()
                .template("{bar:40} {msg} ({eta})")
                .unwrap(),
        );
        Self {
            bp,
            current: self.current,
        }
    }

    /// Sets a message to the [MetroProgressBar].
    pub fn set_message(&self, msg: impl Into<Cow<'static, str>>) {
        self.bp.set_message(msg);
    }

    /// Increments the progress bar by one.
    ///
    /// The bar is refreshed only periodically.
    pub fn inc(&self) {
        let mut current = self.current.lock().unwrap();
        *current += 1;
        if current.is_multiple_of(UPDATE) {
            self.bp.inc(UPDATE);
        }
    }

    /// Sets the progress bar to finished.
    pub fn finish(&self) {
        self.bp.finish_and_clear();
    }

    /// Hides the progress bar temporarily.
    pub fn suspend<F: FnOnce() -> R, R>(&self, f: F) -> R {
        self.bp.suspend(f)
    }
}

/// A spinner.
#[derive(Debug)]
pub struct Spinner(ProgressBar);

impl Spinner {
    /// Starts a [Spinner] with the given message.
    pub fn new(msg: &str) -> Self {
        let bp = if log_enabled!(Level::Info) {
            ProgressBar::new(1).with_message(msg.to_owned())
        } else {
            ProgressBar::hidden()
        };
        bp.set_style(
            ProgressStyle::default_spinner()
                .template("{spinner} {msg}")
                .unwrap(),
        );
        bp.enable_steady_tick(UPDATE_MS);
        Spinner(bp)
    }

    /// Sets the spinner to finished.
    pub fn finish(&mut self) {
        self.0.finish_and_clear();
    }
}
