// This file is part of Metropolis-Core.
// Copyright © 2022, 2023, 2024, 2025 André de Palma, Lucas Javaudin
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Everything related to logging.
use std::fs::File;
use std::path::{Path, PathBuf};
use std::sync::{LazyLock, Mutex};

use anyhow::{Context, Result};
use hashbrown::HashMap;
use log::{warn, LevelFilter};
use simplelog::{
    ColorChoice, CombinedLogger, Config, SharedLogger, TermLogger, TerminalMode, WriteLogger,
};

static SENT_WARNINGS: LazyLock<Mutex<HashMap<WarningType, usize>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
/// Enum representing the various type of warning messages that can be sent.
pub(crate) enum WarningType {
    /// Warning for the AlphaBetaGamma schedule-utility type being deprecated.
    DeprecatedAlphaBetaGamma,
}

/// Sends a warning message if it was sent less than `n` times before.
pub(crate) fn send_warning_at_most_n_times(warn_type: WarningType, message: &str, n: usize) {
    let mut sent_warnings = LazyLock::force(&SENT_WARNINGS).lock().unwrap();
    match sent_warnings.get(&warn_type) {
        Some(count) if *count >= n => {
            // The warning message was already sent at least `n` times.
        }
        _ => {
            // Send the warning message.
            warn!("{}", message);
            *sent_warnings.entry(warn_type).or_insert(0) += 1;
        }
    }
}

/// Sends a warning message if it was never sent before.
pub(crate) fn send_warning_at_most_once(warn_type: WarningType, message: &str) {
    send_warning_at_most_n_times(warn_type, message, 1)
}

/// Initializes logging to a file and terminal.
pub fn initialize_logging<W: std::io::Write + Send + 'static>(
    output: &Path,
    maybe_writer: Option<W>,
) -> Result<()> {
    let log_filename: PathBuf = [output.to_str().unwrap(), "log.txt"].iter().collect();
    let log_file = File::create(log_filename).expect("Failed to create log file");
    let mut loggers: Vec<Box<dyn SharedLogger>> = vec![
        TermLogger::new(
            LevelFilter::Info,
            Config::default(),
            TerminalMode::Mixed,
            ColorChoice::Auto,
        ),
        WriteLogger::new(LevelFilter::Debug, Config::default(), log_file),
    ];
    if let Some(writer) = maybe_writer {
        loggers.push(WriteLogger::new(
            LevelFilter::Info,
            Config::default(),
            writer,
        ));
    }
    CombinedLogger::init(loggers).context("Failed to initialize logging")
}
