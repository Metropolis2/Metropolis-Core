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

// Prevents additional console window on Windows in release, DO NOT REMOVE!!
#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

#[cfg(feature = "tauri")]
use tauri;
#[cfg(feature = "tauri")]
use tauri::Window;
#[cfg(not(target_env = "msvc"))]
use tikv_jemallocator::Jemalloc;

#[cfg(not(target_env = "msvc"))]
#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

#[cfg(feature = "tauri")]
#[tauri::command]
async fn run_simulation(path: String, window: Window) {
    metropolis::run_simulation_impl(path, window).await
}

#[cfg(feature = "tauri")]
#[tauri::command]
async fn run_routing(path: String, window: Window) {
    metropolis::run_routing_impl(path, window).await
}

#[cfg(feature = "tauri")]
#[expect(clippy::disallowed_types)]
fn main() {
    tauri::Builder::default()
        .invoke_handler(tauri::generate_handler![run_simulation, run_routing])
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}

#[cfg(not(feature = "tauri"))]
fn main() {}
