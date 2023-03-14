# Changelog

Changes starting with tag [USER] are of interest to end-users.
Changes starting with tag [DEV] are of interest to developers only.

The tag [INPUT] indicates changes affecting the input files.
The tag [OUTPUT] indicates changes affecting the output files.

## [Unreleased]

### Added

- [DEV] Add a debug check that all agents have reached their destination.

### Changed

- [USER] The progress bars refresh only periodically, for improved speed and better ETA.

### Fixed

- [USER] Fix the progress bar of the within-day model.
- [USER] Fix how waiting times and road length are recorded so that expected travel times are more
  accurate.
- [USER] Fix how the spillback indicator is computed and reset.

## [0.4.0] - 2023-03-12

### Added

- [INPUT] Now road-network parameter `spillback` can be used to prevent vehicles from entering the
  edge if it is full (i.e., if the length of vehicles already on the edge is not smaller than the
  total length of the edge).
- [DEV] Add integration tests `spillback` and `gridlock` for the new spillback feature.

### Changed

- [INPUT] The entry bottleneck and exit bottleneck of an edge must now have exactly the same flow.
  Road-edge parameter `bottleneck_flow` is used to set the bottleneck flow of an edge. (Former
  parameters `bottleneck_inflow` or `bottleneck_outflow` can be used as alias but only one of them
  must be set).
- [DEV] The signature of the `execute` function of events is simplified.
- [DEV] The `VehicleEvent`, `RoadEdgeState`, `RoadNetworkState` and `NetworkState` structs no
  longer hold references to simulation variables.
- [DEV] The `EdgeEntryState` and `EdgeExitState` structs replace the `Bottleneck` struct.
- [DEV] The `RoadNodeState` struct is now empty.

## [0.3.1] - 2023-03-07

### Fixed

- [DEV] Fix Linux build.

## [0.3.0] - 2023-03-07

### Added

- [INPUT] The number of threads to use for parallelized tasks can be specified in the parameters of
  the `metropolis` and `compute_travel_times` scripts (key is `nb_threads`).
- [USER] Add "Congestion and spillback modeling" section to the Book.

### Changed

- [INPUT] Road-network parameter `recording_interval` specifies the distance between breakpoints for
  *all* piecewise-linear functions there are in Metropolis.
- [INPUT] The JSON representation of travel-time functions has changed (see the Book for details).

### Removed

- [INPUT] All the `*_simplification` road-network parameters are removed (`recording_interval`
  parameter has superseded them).
- [DEV] The `Simplification` and `NoSimplification` PwlTTF variants are removed as they are no
  longer needed.

## [0.2.1] - 2023-02-18

### Changed

- [DEV] Build Linux releases using MUSL for large compatibility.

## [0.2.0] - 2023-02-18

### Added

- [INPUT] Add `Trip` mode which can represent trips by car (or any other mode) with
  intermediary stops. See the Book for more details.
- [USER] The simulation can be run with other initial weights than free flow, with the new
  `--weights` command line argument.
- [INPUT] The initial iteration counter to use for the simulation can be specified in the
  parameters of the simulation (variable `init_iteration_counter`).
- [INPUT] New type for the field `utility_model` for road modes: `Polynomial`, which takes as
  values degree 0, 1, 2, 3 and 4 coefficients of a polynomial function (constant, linear, quadratic
  and cubic functions are special cases of the `Polynomial` type).
- [OUTPUT] Add graph of arrival-times distribution for the last iteration in the HTML report.
- [OUTPUT] Add global free-flow travel time (OD free-flow travel time over any route) and global
  congestion to the output.
- [OUTPUT] Add road- and virtual- legs specific results in the report table.
- [USER] Add `CHANGELOG.md` to release zips.
- [USER] Add tags [USER] and [DEV] in the Changelog to specify the concerned individuals (end-users
- [USER] Add tags [INPUT] and [OUTPUT] in the Changelog to indicate that input or output files are
  affected.
- [USER] Add `compute_travel_times` executable (script to run many time-dependent routing queries).
- [USER] Add JSON Schemas for the `compute_travel_times` script in the directory `schemas/tch/`.
- [USER] Add `book` directory with a documentation for Metropolis (in progress).
- [DEV] Add a way not to simplify a `PwlXYF` when building it so that all breakpoints are kept.
- [DEV] Add functions `constrain_to_domain`, `add_x_breakpoints`, `add_z_breakpoints`,
  `into_points`, `into_xs_and_ys` and `iter_eval` to `PwlXYF`.
- [DEV] Add integration test `legs` for the new `Leg` mode.
- [DEV] Add functions `route_free_flow_travel_time` and `route_length` to `RoadNetwork`.

### Changed

- [INPUT] [OUTPUT] The list of points for the piecewise-linear functions is serialized /
  deserialized as an array of arrays `[x, y]` (previously, it was an array of objects with keys `x`
  and `y`).
- [OUTPUT] The route taken by the agent (in the agent results) is serialized as an array of arrays
  `[e, t]`, where `e` is the edge index and `t` is the entry time on the edge (previously it was an
  array of objects with keys `edge` and `edge_entry`).
- [USER] Complete the example so that it include all possible input formats.
- [INPUT] Rename attribute `length` of a vehicle to `headway` for clarity (`length` is set as an
  alias for backward compatibility).
- [USER] Validate that value `t_star_high` is not smaller than value `t_star_low` for the
  alpha-beta-gamma model.
- [USER] Add attribute `readOnly` to parameters `min` and `max` of `PwlXYF` in the JSON Schemas, so
  that the schema is consistent with the actual deserialization process.
- [USER] Various improvements to the `compute_travel_times` script (can output route, can guess best
  algorithm to use, etc.).
- [USER] JSON Schema files are organized in the directory `schemas/metropolis/` and named
  differently.
- [USER] Metropolis executable is now stored in the `execs` directory.
- [DEV] Rename `XYF` function `middle_departure_time` to `middle_x` to be consistent with the
  terminology for the `XYF` functions.
- [DEV] Add a `static` lifetime requirement for `TTFNum` trait.
- [DEV] Enum `ModeResults` and struct `TripResults` are used to store mode-specific pre-day and
  within-day results. Previously, pre-day results were stored in `PreDayChoices` and `RoadChoices`,
  while within-day results were stored in `ModeResults` and `RoadResults`.
- [DEV] Trait `Event` now takes a timeline, allowing to use references to the simulation input in
  the events.

### Removed

- [INPUT] The mode `Road` is removed (all the features are available with the new `Trip` mode).
- [INPUT] Parameters `schedule_utility` for an Agent is removed. The schedule utility is now
  specified at the mode-level.
- [Input] The parameter `desired_arrival` for `AlphaBetaGammaModel` is removed. The schedule utility
  is now explicitely specified for either the origin or destination (or intermediary stop) making
  this parameter useless.
- [DEV] The `PreDayResult` struct is removed (everything is stored directly in `AgentResult` and
  `ModeResults` now).

### Deprecated

- [INPUT] The types `None`, `Proportional` and `Quadratic` for field `utility_model` raise a
  deprecated warning when used.

### Fixed

- [USER] Deserialize `null` values for constant travel-time functions as `Infinity`, consistently
  with how the such values are serialized.
- [DEV] Make functions `iter_eval` and `add_x_breakpoints` for `PwlXYF` works properly for points
  after the last point of the `PwlXYF`.
- [DEV] Run Clippy with `cargo-make`.
- [DEV] Run the examples with `cargo-make`.

## [0.1.7] - 2023-01-05

### Modify

- [DEV] When generating JSON schemas, output directory is automatically created if it does not
  exist.

## [0.1.6] - 2023-01-05

### Added

- [USER] Allowed / restricted edges can be specified for each vehicle type through fields
  `allowed_edges` and `restricted_edges`.

### Changed

- [DEV] In the pre-processing of the road network, a set of unique vehicle types is computed (two
  vehicle types are considered identical if they can share the same network weights and skims,
  i.e., they have the same speed function, allowed edges and restricted edges).
- [USER] Road network weights and skims are stored and computed for each _unique_ vehicle type
  (previously, this was done for each vehicle type).
- [DEV] Some tweaks were done for `cargo-make` (e.g., no verbose output, Clippy by default).

### Fixed

- [DEV] Various fixes for GitHub Actions.
- [USER] Fix `EdgeIndex` not properly document in the JSON Schemas.

## [0.1.5] - 2022-12-21

### Added

- [DEV] The Changelog is automatically added to the GitHub releases.

### Changed

- [DEV] Do not compile all features by default with `cargo-make`.

### Fixed

- [DEV] Fix compiling with `cargo-make` on Windows and MacOS.
- [USER] Fix links to releases in the Changelog.

## [0.1.4] - 2022-12-20

### Added

- [DEV] Add `Makefile.toml` to control the behavior of `cargo-make`.
- [USER] Add this changelog.
- [USER] Add README file.

## [0.1.3] - 2022-12-20

### Fixed

- [DEV] Install `cargo-make` during the `publish` workflow.

## [0.1.2] - 2022-12-20

### Fixed

- [DEV] Fix the filter used to detect tags of new releases.

## [0.1.1] - 2022-12-20

### Added

- [DEV] Use `cargo-make` and GitHub Actions to automate building, testing and releasing new versions.

### Changed

- [USER] New format for logs.
- [USER] Default log level is INFO for logs to stdout and DEBUG for logs to file.
- [DEV] Do not output source code in the documentation.

### Fixed

- [DEV] Feature Jemalloc is disabled for Windows.
- [DEV] Fix License filename.

### Security

- [DEV] Remove `chrono` dependency that depends on a vulnerable version of `time`.

## [0.1.0] - 2022-12-12

### Added

- First release of Metrolib, there are two many things to list.

[unreleased]: https://github.com/MetropolisTHEMA/Metrolib/compare/0.4.0...HEAD
[0.4.0]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.4.0
[0.3.1]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.3.1
[0.3.0]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.3.0
[0.2.1]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.2.1
[0.2.0]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.2.0
[0.1.7]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.1.7
[0.1.6]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.1.6
[0.1.5]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.1.5
[0.1.4]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.1.4
[0.1.3]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.1.3
[0.1.2]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.1.2
[0.1.1]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.1.1
[0.1.0]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.1.0
