const { invoke } = window.__TAURI__.tauri;
const { open } = window.__TAURI__.dialog;
const { listen } = window.__TAURI__.event;

// Open File Dialog
async function fileselect() {
  open({
    multiple: false,
    filters: [
      {
        name: "json",
        extensions: ["json"],
      },
    ],
  }).then((path) => {
    if (path) {
      pathBox.innerHTML = path;
      runButton.removeAttribute("disabled");
    }
  });
}

async function listenlog() {
  await listen("log-event", (event) => {
    logBox.innerHTML += event.payload.message;
  });
}

async function listenrun() {
  await listen("run-done", (_) => {
    runButton.innerHTML = "Done!";
  });
}

async function listenrunfailed() {
  await listen("run-failed", (_) => {
    runButton.innerHTML = "Failed!";
  });
}

async function runsimulation() {
  runButton.setAttribute("disabled", "disabled");
  openButton.setAttribute("disabled", "disabled");
  runButton.innerHTML = "Running simulation...";
  var path = pathBox.innerHTML;
  invoke("run_simulation", { path: path });
  listenrun();
  listenrunfailed();
}

let openButton;
let runButton;
let logBox;
let pathBox;

window.addEventListener("DOMContentLoaded", () => {
  openButton = document.querySelector("#open-button");
  runButton = document.querySelector("#run-button");
  pathBox = document.querySelector("#path-box");
  logBox = document.querySelector("#log-box");

  openButton.addEventListener("click", (_) => {
    fileselect();
  });

  runButton.addEventListener("click", (_) => {
    runsimulation();
  });

  listenlog();
});
