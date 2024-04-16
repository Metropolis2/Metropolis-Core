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
#[allow(clippy::disallowed_types)]
fn main() {
    tauri::Builder::default()
        .invoke_handler(tauri::generate_handler![run_simulation, run_routing])
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}

#[cfg(not(feature = "tauri"))]
fn main() {}
