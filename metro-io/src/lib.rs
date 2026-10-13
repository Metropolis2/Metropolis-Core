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

//! Input / output utilities shared by the Metropolis-Core crates.
//!
//! - [MetroId]: identifiers read from the input files (integers or strings).
//! - [read]: read CSV or Parquet files and extract typed columns from them.
//! - [write]: convert data to arrow format and write it as CSV or Parquet files.
//! - [json]: read and write (possibly zstd-compressed) JSON files.
//! - [hash]: hash map and hash set types with a fixed-seed hasher.

pub mod hash;
mod id;
pub mod json;
pub mod read;
pub mod write;

pub use id::MetroId;
