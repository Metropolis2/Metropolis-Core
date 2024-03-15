// Prevents additional console window on Windows in release, DO NOT REMOVE!!
#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

use std::fmt::Write;
use std::{io, path::PathBuf};

use metropolis::run_simulation_with_writer;
use serde::Serialize;
use tauri::Window;

#[derive(Debug, Default, Clone, Serialize)]
struct Payload {
    message: String,
}

#[derive(Debug, Clone)]
struct GUILogWriter {
    window: Window,
}

impl io::Write for GUILogWriter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let message = std::str::from_utf8(buf)
            .unwrap()
            .replace('\n', "<br>")
            .replacen("[INFO]", "<span style=\"color:blue;\">[INFO]</span>", 1)
            .replacen("[WARN]", "<span style=\"color:orange;\">[WARN]</span>", 1)
            .replacen("[ERROR]", "<span style=\"color:red;\">[ERROR]</span>", 1)
            .to_owned();
        self.window.emit("log-event", Payload { message }).unwrap();
        Ok(buf.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[tauri::command]
async fn run_simulation(path: String, window: Window) {
    let writer = GUILogWriter {
        window: window.clone(),
    };
    let res = run_simulation_with_writer(&PathBuf::from(path), writer);
    if let Err(e) = res {
        let error_msg: String = e
            .chain()
            .enumerate()
            .fold(String::new(), |mut msg, (i, cause)| {
                let _ = write!(msg, "<br>&emsp;{i}: {cause}");
                msg
            });
        let message =
            format!("<span style=\"color:red;\">ERROR: {error_msg}</span>").replace('\n', "<br>");
        window.emit("log-event", Payload { message }).unwrap();
        window.emit("run-failed", ()).unwrap();
    } else {
        window.emit("run-done", ()).unwrap();
    }
}

#[allow(clippy::disallowed_types)]
fn main() {
    tauri::Builder::default()
        .invoke_handler(tauri::generate_handler![run_simulation])
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}
