use gtk::prelude::*;
use gtk::{gio, glib, Application};
use metropolis::gui::Window;
const APP_ID: &str = "org.metropolis.gui";

fn main() -> glib::ExitCode {
    // Register and include resources
    gio::resources_register_include!("metropolis.gresource")
        .expect("Failed to register resources.");

    // Create a new application
    let app = Application::builder().application_id(APP_ID).build();

    // Connect to "activate" signal of `app`
    app.connect_activate(build_ui);

    // Run the application
    app.run()
}

fn build_ui(app: &Application) {
    // Create a new custom window and present it
    let window = Window::new(app);
    window.present();
}
