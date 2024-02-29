# METROPOLIS2

METROPOLIS2 is a dynamic multi-modal agent-based transport simulator.

## Releases

A release of METROPOLIS2 consists in a zip file with the following content:

- `examples/`: example input files for the simulator
- `execs/`: directory where the executables are stored
- `schemas/`: JSON Schemas for the various input and output files (as JSON, HTML and Markdown)
- `CHANGELOG.md`: file which list the changes between versions
- `LICENSE.txt`: file with METROPOLIS2' License
- `README.md`: this file

The versions of METROPOLIS2 are given a version number MAJOR.MINOR.PATCH (e.g., `0.1.7`).
While METROPOLIS2 is still in Major version zero (0.y.z), an increment of the minor version
indicates a backwards _incompatible_ change which means that the input files from the previous
version might not work with the new version.
