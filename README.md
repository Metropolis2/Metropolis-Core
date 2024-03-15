# METROPOLIS2

METROPOLIS2 is a dynamic multi-modal agent-based transport simulator.

## Releases

A release of METROPOLIS2 consists in a zip file with the following content:

- `examples/`: example input files for the simulator
- `execs/`: directory where the executables are stored
- `CHANGELOG.md`: file which list the changes between versions
- `LICENSE.txt`: file with METROPOLIS2' License
- `README.md`: this file

The versions of METROPOLIS2 are given a version number MAJOR.MINOR.PATCH (e.g., `2.1.3`), following
the SemVer specification.
An increase of the MAJOR number indicates backward incompatibilities with previous versions.
An increase of the MINOR number indicates new features, that are backward-compatible.
An increase of the PATCH number indicates bug fixes.

## Executables

METROPOLIS2 comes with 4 executables:

- `metropolis_gui`: A GUI (Graphical User Interface) to run a simulation interactively.
- `metropolis_cli`: A CLI (Command Line Interface) to run a simulation from the terminal.
- `compute_travel_decisions`: A CLI to compute the travel decisions of a population, without running
  the full simulator.
- `compute_travel_times`: A CLI to compute (time-dependent) travel times for a collection of
  origin-destination pairs.

## How to use

To run `metropolis_gui`, simply double click on the executable, choose your input parameters file
and click on the `Run` button.
The simulation will start and display the log in the window below the `Run` button.

To run `metropolis_cli`, open a terminal and execute the following command (on Linux or MacOS):
```
./metropolis_cli [path_to_parameters.json]
```
or (on Windows):
```
.\metropolis_cli.exe [path_to_parameters.json]
```

## Example simulation

The directory `examples/` contains a very basic example simulation, with no meaningful
interpretation.
This example simulation makes use of all the possible input values so it is a great way to test if
the simulator is running properly.

In the `examples/data/` directory, there are three subdirectories corresponding to three different
input formats for the same simulation (CSV, Parquet or Parquet with unnested structs).

The Python script `examples/generate_input.py` is used to generate the example simulation in the
three different formats.
Feel free to use it as a an example to create your own input files.
