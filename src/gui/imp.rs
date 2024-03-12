use std::ops::Deref;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::{Arc, Mutex};

use glib::clone;
use glib::subclass::InitializingObject;
use gtk::gio::File;
use gtk::glib::subclass::ObjectImplRef;
use gtk::glib::Error;
use gtk::subclass::prelude::*;
use gtk::{gio, ApplicationWindow, DialogError, TextView};
use gtk::{glib, Button, CompositeTemplate};
use gtk::{prelude::*, FileDialog};

use crate::run_simulation;

// Object holding the state
#[derive(CompositeTemplate, Default)]
#[template(resource = "/org/metropolis/gui/window.ui")]
pub struct Window {
    #[template_child]
    pub input_button: TemplateChild<Button>,
    #[template_child]
    pub input_text: TemplateChild<TextView>,
    #[template_child]
    pub run_button: TemplateChild<Button>,
    // #[template_child]
    // pub scrolled_window: TemplateChild<ScrolledWindow>,
    #[template_child]
    pub log: TemplateChild<TextView>,
    /// Path to the `parameters.json` file.
    pub path: Arc<Mutex<PathBuf>>,
    /// True if the simulation run is finished.
    pub is_finished: Arc<Mutex<bool>>,
    pub error: Arc<Mutex<String>>,
}

// The central trait for subclassing a GObject
#[glib::object_subclass]
impl ObjectSubclass for Window {
    // `NAME` needs to match `class` attribute of template
    const NAME: &'static str = "MetroWindow";
    type Type = super::Window;
    type ParentType = gtk::ApplicationWindow;

    fn class_init(klass: &mut Self::Class) {
        klass.bind_template();
        klass.bind_template_callbacks();
    }

    fn instance_init(obj: &InitializingObject<Self>) {
        obj.init_template();
    }
}

// Trait shared by all GObjects
impl ObjectImpl for Window {
    fn constructed(&self) {
        // Call "constructed" on parent
        self.input_text
            .buffer()
            .set_text("Select parameters JSON file...");
        self.run_button.set_sensitive(false);
        self.parent_constructed();
    }
}

#[gtk::template_callbacks]
impl Window {
    #[template_callback]
    fn input_button_clicked(&self, _input_button: &Button) {
        let file_dialog = FileDialog::builder()
            .accept_label("Select")
            .modal(true)
            .title("Select input file")
            .build();
        let path = Arc::clone(&self.path);
        file_dialog.open(
            None::<&ApplicationWindow>,
            None::<&gio::Cancellable>,
            clone!(
                    @weak self as this => move |r| {
                        input_callback(r, path, this)
                    }
            ),
        );
    }

    #[template_callback]
    fn run_button_clicked(&self, run_button: &Button) {
        run_button.set_sensitive(false);
        self.input_button.set_sensitive(false);
        run_button.set_label("Running...");
        let path: PathBuf = self.path.lock().unwrap().clone();
        let writer = Rc::new(Mutex::new(self.log.buffer()));
        let is_finished = self.is_finished.clone();
        let parameters = crate::io::json::get_parameters_from_json(&path).expect("TODO");
        let log_filename: PathBuf = [parameters.output_directory.to_str().unwrap(), "log.txt"]
            .iter()
            .collect();
        let filename2 = log_filename.clone();
        glib::timeout_add_seconds_local(1, move || {
            if *is_finished.lock().unwrap().deref() {
                return glib::ControlFlow::Break;
            }
            if log_filename.is_file() {
                let s = std::fs::read_to_string(&log_filename).unwrap();
                let lock = writer.lock().unwrap();
                if s.len() != lock.char_count() as usize {
                    lock.set_text(&s);
                }
                if s.len() > 4 && &s[s.len() - 5..] == "Done\n" {
                    // Small hack to know when the run is finished.
                    return glib::ControlFlow::Break;
                }
            }
            glib::ControlFlow::Continue
        });
        let error = self.error.clone();
        let (sender, receiver) = async_channel::bounded(1);
        gio::spawn_blocking(move || {
            let sender = sender.clone();
            let res = run_simulation(&path);
            if let Err(e) = res {
                let s = if filename2.is_file() {
                    std::fs::read_to_string(&filename2).unwrap()
                } else {
                    String::new()
                };
                let mut lock = error.lock().unwrap();
                *lock = format!("{}\n{:?}", s, e);
                sender
                    .send_blocking(Err(format!("{}\n{:?}", s, e)))
                    .unwrap_or_else(|e| panic!("Sending error: {e}"));
            } else {
                sender
                    .send_blocking(Ok(()))
                    .unwrap_or_else(|e| panic!("Sending error: {e}"));
            }
        });
        let writer = Rc::new(Mutex::new(self.log.buffer()));
        let is_finished = self.is_finished.clone();
        glib::spawn_future_local(async move {
            while let Ok(res) = receiver.recv().await {
                *is_finished.lock().unwrap() = true;
                match res {
                    Ok(_) => (),
                    Err(string) => {
                        let lock = writer.lock().unwrap();
                        lock.set_text(&string);
                    }
                }
            }
        });
    }
}

// Trait shared by all widgets
impl WidgetImpl for Window {}

// Trait shared by all windows
impl WindowImpl for Window {}

// Trait shared by all application windows
impl ApplicationWindowImpl for Window {}

fn input_callback(
    result: Result<File, Error>,
    path_cell: Arc<Mutex<PathBuf>>,
    this: ObjectImplRef<Window>,
) {
    match result {
        Ok(file) => {
            let path: PathBuf = file.path().expect("Invalid path");
            let mut my_path = path_cell.lock().unwrap();
            this.input_text.buffer().set_text(&format!("{path:?}"));
            this.run_button.set_sensitive(true);
            *my_path = path;
        }
        Err(e) => {
            if let Some(dialog_error) = e.kind::<DialogError>() {
                match dialog_error {
                    DialogError::Cancelled => println!("Cancelled"),
                    DialogError::Dismissed => println!("Dismissed"),
                    DialogError::Failed => println!("Failed"),
                    _ => (),
                }
            } else {
                println!("Err: {e:?}");
            }
        }
    }
}
