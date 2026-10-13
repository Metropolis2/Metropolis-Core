# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project overview

Metropolis-Core is the Rust-based core of the METROPOLIS2 simulator, a dynamic
multi-modal agent-based transport simulator. It is a Cargo workspace with five
member crates:

- `metropolis-core` — the simulator itself: reads a `parameters.json` + population/network
  input files, runs the day-to-day agent-based simulation, and writes results. Produces
  the `metropolis_cli` binary.
- `tch` — Time-dependent Contraction Hierarchies: a standalone routing/shortest-path
  library (Dijkstra, bidirectional search, contraction hierarchies, profile queries over
  time-dependent travel-time functions). Produces the `routing_cli` binary. Depends on `pwl`.
- `pwl` (crate name `ttf`) — piecewise-linear travel-time functions (TTFs), the core math
  primitive used to represent time-dependent travel times/costs across the workspace.
- `choice` — discrete/continuous choice models (deterministic argmax and Logit), used by
  `metropolis-core` for mode/route/departure-time choice.
- `metro-io` (crate name `metro_io`) — code shared by `metropolis-core` and `tch`: the `MetroId`
  identifier type (with its global string interner), the fixed-seed `hash::{HashMap, HashSet}`
  aliases, reading CSV/Parquet files into typed columns (`read`), writing `ToArrow` data as
  CSV/Parquet (`write`) and (zstd-compressed) JSON helpers (`json`). Both crates re-export
  `metro_io::hash` as `crate::hash` and `MetroId` (`metropolis_core::units::MetroId`,
  `tch::tools::MetroId`).

`tch-python` (pyo3 bindings exposing `tch`'s graph/routing types to Python) exists in the
tree but is **not** yet a workspace member (not listed in the root `Cargo.toml`
`[workspace] members`) — treat it as work in progress.

Dependency graph: `metropolis-core` → `tch`, `choice`, `pwl` (`ttf`), `metro-io`;
`tch` → `pwl`, `metro-io`; `choice` → `pwl`.

## Common commands

Build/test/lint everything the way CI does (`cargo make ci-flow`, mirrored by
`.github/workflows/ci.yml`) requires [cargo-make](https://sagiegurari.github.io/cargo-make/).
For local iteration, plain `cargo` sub-commands work directly since this is a normal
Cargo workspace:

```shell
# Build the simulator binary (release)
cargo build --release -p metropolis-core

# Build the routing binary (release)
cargo build --release -p tch

# Run all tests in the workspace
cargo test --workspace

# Run a single test file / test
cargo test -p metropolis-core --test bottleneck
cargo test -p metropolis-core --test bottleneck some_test_name

# Run workspace examples (integration-style tests live here too)
cargo test --workspace --examples

# Lint (clippy is a warn-as-error gate in CI via `all = "warn"` + disallowed types)
cargo clippy --workspace

# Format
cargo fmt --all

# Full local CI-equivalent flow (format, format toml, clippy, build, test, test-examples)
cargo make            # runs `dev-test-flow` by default
```

Integration tests (`metropolis-core/tests/*.rs`, `tch/tests/*.rs`) construct small
synthetic networks/populations in Rust and assert on simulation results — read one of
them (e.g. `metropolis-core/tests/bottleneck.rs`) as a template for a new test rather
than the example CSV/Parquet data.

Sample input data usable for manual runs of `metropolis_cli` lives in
`metropolis-core/examples/data/` (CSV and Parquet variants of the same scenario);
`metropolis-core/examples/generate_input.py` and `tch/examples/generate_input.py`
regenerate the example input files. Run the built binary directly with a
`parameters.json` path, e.g. `./target/release/metropolis_cli path/to/parameters.json`.

## Code conventions

- **Newtype units everywhere**: `metropolis-core/src/units.rs` defines wrapper types
  (`Time`, `Length`, `Speed`, `ValueOfTime`, `PCE`, `Flow`, `Utility`, `MetroId`, etc.) so
  quantities in different units can't be mixed by accident. When adding new numeric
  fields, prefer reusing/extending these types over raw `f64`/`usize`.
- **Fixed-seed hash maps**: `clippy.toml` disallows `std::collections::HashMap`/`HashSet`
  and `hashbrown::HashMap`/`HashSet` (randomly seeded, so iteration order would vary between
  runs); use `crate::hash::{HashMap, HashSet}` (re-exported from `metro_io::hash`) or
  `rustc_hash::{FxHashMap, FxHashSet}` where already used, e.g. in `network/road_network`.
- **Global singletons via `OnceLock`**: cross-cutting simulation state — parameters
  (`parameters.rs`), population (`population.rs`), network (`network/mod.rs`) — is
  initialized once into a module-level `OnceLock` (`init`/`replace` functions) and read
  through accessor functions rather than passed around as arguments everywhere.
- Workspace-wide lint config lives in the root `Cargo.toml` under `[workspace.lints]`
  (rust lints + `clippy::all = "warn"`) and is inherited by every member crate via
  `[lints] workspace = true`.
- `rustfmt.toml` groups imports as `StdExternalCrate` (std, then external, then crate-
  local, each in their own group) — keep new `use` blocks consistent with this.
- License headers (GPL-3.0-or-later boilerplate) are present at the top of essentially
  every source file; match this when adding new files.

## Architecture notes (`metropolis-core`)

The simulation is agent-based and iterates day-to-day (`simulation/mod.rs` drives the
top-level loop):

1. **Population** (`population.rs`): a fixed global `Vec<Agent>`, each agent choosing
   among one or more `Mode`s of transportation on each iteration.
2. **Network** (`network/mod.rs`, `network/road_network/`): currently the road network is
   the primary supply side. `road_network/preprocess.rs` builds preprocessing data
   (including contraction hierarchies from `tch`), `weights.rs` holds per-edge travel-time
   functions, `skim.rs` computes earliest-arrival/travel-time skims via `tch` queries, and
   `state.rs`/`vehicle.rs` track simulated dynamics.
3. **Modes** (`mode/mod.rs`, `mode/trip/`): each mode resolves to one or more `Leg`s of
   travel; trip-level results and events are in `mode/trip/results.rs` and
   `mode/trip/event.rs`.
4. **Events** (`event.rs`): the within-day simulation is event-driven, using a
   multi-queue `BinaryHeap`-based priority queue (`Q = 256` sub-queues) of objects
   implementing the event trait.
5. **Utility models**: `travel_utility.rs` (utility as a function of travel time) and
   `schedule_utility/` (utility as a function of departure/arrival time, e.g. the
   alpha-beta-gamma model in `schedule_utility/alpha_beta_gamma.rs`) feed into `choice`
   (the `choice` crate) to pick routes/modes/departure times.
6. **Learning** (`learning.rs`): day-to-day learning models (e.g. exponential smoothing)
   determine how agents update beliefs (e.g. expected travel times) between iterations
   based on the previous day's simulated outcomes.
7. **I/O** (`io/`): parameters are read from JSON (`io/json.rs`); population/network data
   is read from CSV or Parquet files in `io/input.rs` (with `metro_io::read::Columns`), and
   results are converted to arrow in `io/output.rs` (`metro_io::write::ToArrow` impls) then
   written with `metro_io::write::{write_csv, write_parquet}`. `report.rs` +
   `templates/report.html` (Askama template) generate an HTML summary report of simulation
   results.

`tch` is a separable routing engine: `contraction_hierarchies.rs` builds the hierarchy
over a `petgraph::DiGraph`, `bidirectional_search.rs`/`bidirectional_ops.rs` implement
bidirectional Dijkstra variants (plain, profile/time-dependent, TCH-accelerated), and
`algo.rs`/`query.rs` expose the query API (earliest-arrival and profile queries) that
`metropolis-core`'s `road_network/skim.rs` calls into. Time-dependent edge weights are
represented as `TTF`s from the `pwl` crate throughout.

## Release process

See `how_to_update.md`: bump the version in `metropolis-core/Cargo.toml`, `CITATION.cff`,
and `Makefile.toml`, update `CHANGELOG.md`, run `cargo update`, commit as
`"Update to x.y.z"`, push, then tag with `git tag -a x.y.z -m x.y.z` and push tags. The
`publish.yml` workflow builds and attaches release binaries for Linux/Windows/macOS when
a version tag is pushed.
