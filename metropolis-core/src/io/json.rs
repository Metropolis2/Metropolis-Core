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

//! Imports / exports through JSON files.

use std::path::Path;

use anyhow::{Context, Result};
use metro_io::json::read_json;

use crate::parameters::Parameters;

/// Deserializes parameters from JSON files.
pub fn get_parameters_from_json(path: &Path) -> Result<Parameters> {
    read_json(path).context("Failed to read parameters")
}
