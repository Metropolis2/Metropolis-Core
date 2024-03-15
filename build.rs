#[cfg(feature = "tauri")]
fn main() {
    tauri_build::build()
}

#[cfg(not(feature = "tauri"))]
fn main() {}
