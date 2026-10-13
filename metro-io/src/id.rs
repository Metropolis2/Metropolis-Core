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

//! Identifiers of the objects read from the input files.
use std::fmt;
use std::sync::{LazyLock, RwLock};

use enum_as_inner::EnumAsInner;
use serde::Serialize;

use crate::hash::HashMap;

// String ids used in the simulation.
static STRING_INTERNER: LazyLock<RwLock<StringInterner>> = LazyLock::new(Default::default);

/// A Struct to store the String ids used in the simulation.
#[derive(Default, Debug)]
struct StringInterner {
    // string -> index
    map: HashMap<String, u32>,
    // index -> string
    strings: Vec<String>,
}

impl StringInterner {
    /// Stores a new value to the STRING_INTERNER.
    fn intern(&mut self, s: impl Into<String>) -> u32 {
        let s = s.into();
        if let Some(&id) = self.map.get(&s) {
            return id;
        }
        let id = self.strings.len() as u32;
        self.strings.push(s.clone());
        self.map.insert(s, id);
        id
    }

    /// Returns the actual String value corresponding to the interner index.
    fn resolve(&self, id: u32) -> Option<String> {
        self.strings.get(id as usize).cloned()
    }
}

/// Representation of an Identifier that can be either integer or string.
#[derive(Copy, Clone, Debug, PartialEq, Hash, EnumAsInner, Serialize)]
pub enum MetroId {
    /// Id represented as an unsigned integer.
    Unsigned(u64),
    /// Id represented as an integer.
    Integer(i64),
    /// Id represented as String.
    /// Only the index of the String in `STRING_INTERNER` is stored so that MetroId can implement
    /// Copy.
    Arbitrary(u32),
}

impl MetroId {
    /// Returns the actual String value corresponding to the stored id.
    ///
    /// Returns None if the id is not `Arbitrary`.
    pub fn resolve_arbitrary(&self) -> Option<String> {
        if let Self::Arbitrary(index) = self {
            STRING_INTERNER.read().unwrap().resolve(*index)
        } else {
            None
        }
    }
}

impl Default for MetroId {
    fn default() -> Self {
        Self::Unsigned(0)
    }
}

impl From<u64> for MetroId {
    fn from(value: u64) -> Self {
        Self::Unsigned(value)
    }
}

impl From<i64> for MetroId {
    fn from(value: i64) -> Self {
        Self::Integer(value)
    }
}

impl From<&str> for MetroId {
    fn from(value: &str) -> Self {
        let index = STRING_INTERNER.write().unwrap().intern(value);
        Self::Arbitrary(index)
    }
}

impl fmt::Display for MetroId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unsigned(i) => {
                write!(f, "{}", i)
            }
            Self::Integer(i) => {
                write!(f, "{}", i)
            }
            Self::Arbitrary(_) => {
                let s = self.resolve_arbitrary().unwrap();
                write!(f, "{}", s)
            }
        }
    }
}

impl Eq for MetroId {}
