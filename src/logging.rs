// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Everything related to logging.
use std::fs::File;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use log::LevelFilter;
use simplelog::{
    ColorChoice, CombinedLogger, Config, SharedLogger, TermLogger, TerminalMode, WriteLogger,
};

/// Initializes logging to a file and terminal.
pub fn initialize_logging(output: &Path) -> Result<()> {
    let log_filename: PathBuf = [output.to_str().unwrap(), "log.txt"].iter().collect();
    let log_file = File::create(log_filename).expect("Failed to create log file");
    let loggers: Vec<Box<dyn SharedLogger>> = vec![
        TermLogger::new(
            LevelFilter::Info,
            Config::default(),
            TerminalMode::Mixed,
            ColorChoice::Auto,
        ),
        WriteLogger::new(LevelFilter::Info, Config::default(), log_file),
    ];
    CombinedLogger::init(loggers).context("Failed to initialize logging")
}
