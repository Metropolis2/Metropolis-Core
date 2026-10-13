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

//! Hash map and hash set types with a fixed-seed hasher.
//!
//! [hashbrown]'s default hasher, `foldhash::fast::RandomState`, derives its seed from ASLR
//! addresses and a global counter, so the iteration order of a map varies from one run of the
//! simulation to another (and even between two maps of the same run). Iterating a map in that
//! order and summing floats, or feeding it to a parallel iterator, makes the results of the
//! simulation depend on the run.
//!
//! `foldhash::fast::FixedState` is the very same hash function with a constant seed instead, so
//! these aliases make the iteration order reproducible at no cost in hashing performance.

/// Hash map with a fixed-seed hasher.
///
/// See the [module documentation](self) for why the default hasher is not used.
#[expect(clippy::disallowed_types)]
pub type HashMap<K, V> = hashbrown::HashMap<K, V, foldhash::fast::FixedState>;

/// Hash set with a fixed-seed hasher.
///
/// See the [module documentation](self) for why the default hasher is not used.
#[expect(clippy::disallowed_types)]
pub type HashSet<T> = hashbrown::HashSet<T, foldhash::fast::FixedState>;
