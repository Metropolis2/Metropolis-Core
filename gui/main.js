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
      routingButton.removeAttribute("disabled");
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
    buttonRow.innerHTML = "<b>Done!</b>";
  });
}

async function listenrunfailed() {
  await listen("run-failed", (_) => {
    buttonRow.innerHTML = "<b>Failed!</b>";
  });
}

async function runSimulation() {
  openButton.setAttribute("disabled", "disabled");
  buttonRow.innerHTML = "<b>Running simulation...</b>";
  var path = pathBox.innerHTML;
  invoke("run_simulation", { path: path });
  listenrun();
  listenrunfailed();
}

async function runRouting() {
  openButton.setAttribute("disabled", "disabled");
  buttonRow.innerHTML = "<b>Running routing...</b>";
  var path = pathBox.innerHTML;
  invoke("run_routing", { path: path });
  listenrun();
  listenrunfailed();
}

let openButton;
let runButton;
let routingButton;
let buttonRow;
let logBox;
let pathBox;

window.addEventListener("DOMContentLoaded", () => {
  openButton = document.querySelector("#open-button");
  runButton = document.querySelector("#run-button");
  routingButton = document.querySelector("#routing-button");
  buttonRow = document.querySelector("#button-row");
  pathBox = document.querySelector("#path-box");
  logBox = document.querySelector("#log-box");

  openButton.addEventListener("click", (_) => {
    fileselect();
  });

  runButton.addEventListener("click", (_) => {
    runSimulation();
  });
  routingButton.addEventListener("click", (_) => {
    runRouting();
  });

  listenlog();
});
