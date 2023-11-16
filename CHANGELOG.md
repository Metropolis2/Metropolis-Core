# Changelog

Changes starting with tag [USER] are of interest to end-users.
Changes starting with tag [DEV] are of interest to developers only.

The tag [INPUT] indicates changes affecting the input files.
The tag [OUTPUT] indicates changes affecting the output files.

## [Unreleased]

### Changed

- [OUTPUT] The iteration results are saved in a single file, `iteration_results.ext`, updated at
  each iteration. Previously they were saved in a different file for each iteration. The filetype
  and extension are based on the `saving_format` parameter (`JSON`, `Parquet` or `CSV`).
- [USER] Congestion is set to zero when free-flow travel time is zero, as a convention. Previously,
  congestion was set to NaN.
- [DEV] Use `debug=false` for dependencies to decrease the binary size.

### Fixed

- [USER] A crash occuring for road legs with same origin as destination is fixed.

## [0.6.0] - 2023-10-24

### Added

- [INPUT] The parameter `saving_format` can be used to choose the format of the output files (only
  for agent results for now). Possible values: `JSON` (default, previous format), `Parquet`, `CSV`.
- [INPUT] An `id` can be specify for the modes and the legs. These ids are then shown in the
  agent-results output.

### Fixed

- [OUTPUT] Utility was not computed correctly for trips with only virtual legs.

## [0.5.2] - 2023-09-15

### Changed

- [OUTPUT] The pre-computed route is no longer stored with the agent results for the
  `compute_choices` executable, instead, it is stored in a separate JSON file.

## [0.5.1] - 2023-09-14

### Changed

- [OUTPUT] In the agent results, the pre-computed route is stored (field `expected_route`) whenever
  the field `route` is empty. For now, this only occurs when running the `compute_choices`
  executable.

### Fixed

- [USER] The order in which ids are stored in the network-weights input is no longer relevant.

## [0.5.0] - 2023-07-28

### Added

- [INPUT] Add mandatory parameter `id` to edges (must be unique and non-negative). This is a
  breaking change. The id is used in the output agent-results file (for the route) and in the
  network weights file (see below).
- [INPUT] Road-network parameter `approximation_bound` can be used to simplify the travel-time
  functions (and thus speed up the routing algorithm) at the cost of a small approximation.
- [OUTPUT] Add route length, route free-flow travel time and global free-flow travel time in the
  output of the `compute_choices` executable (whenever the route is pre-computed).
- [DEV] Add integration test `loop` to check for absence of loops in the routes.

### Changed

- [INPUT] In the road-network input file, node ids no longer have to range from 0 to `n - 1` (where
  `n` is the number of nodes).
- [INPUT] In the network-weights input and output file, the inner array of travel-time functions is
  replaced by an object that maps edge ids (parameter `id` of the edge) to the travel-time function.
  This is a breaking change.
- [USER] Remove loops in the route taken when they are detected, instead of just sending a warning.
- [USER] Compute the expected arrival time more accurately.
- [USER] When a vehicle is forced to be released on the next edge, it does not use any additionnal
  length so that the edge will not stay full for too long.

### Fixed

- [USER] Consider the origin delay when pre-computing routes.

## [0.4.3] - 2023-07-06

### Changed

- [DEV] Updated dependencies

## [0.4.2] - 2023-07-06

### Added

- [INPUT] Can add constant values to each alternative in the `DeterministicChoiceModel`.
- [INPUT] Allow a discrete choice between different departure times for the departure-time choice
  model of `Trip` mode.
- [INPUT] Parameter `pre_compute_route` can be used to compute the routes of the trip in the pre-day
  model instead of the within-day model (better performances). By default, the parameter is `true`.

### Changed

- [USER] Default is to allow overtaking on the edges.

## [0.4.1] - 2023-04-06

### Added

- [INPUT] Add road-network parameter `max_pending_duration` to specify the delay after which
  vehicles are forced to enter the next edge in case of spillback.
- [INPUT] Add edge parameter `overtaking` to allow vehicles to overtake each other at the edge's
  exit bottleneck.
- [INPUT] Add road-network parameter `algorithm_type` to choose the algoritm used for
  origin-destination profile queries (TCH or Intersect). Default is to let the simulator guess the
  best algorithm.
- [INPUT] Network weights can be read directly from the output `weight_results.json.zst` (no need to
  decompress the file). Using a decompressed JSON file is still possible.
- [USER] Add the current time of the events in the within-day model progress bar.
- [USER] Ignore warnings when more than 20 have already been emitted.
- [USER] Add length of route difference in the output.
- [USER] Add `compute_choices` which can be used to compute choices from the pre-day model without
  running a full iteration.
- [DEV] Add a debug check that all agents have reached their destination.
- [DEV] Add more debug checks for the routes computed by the contraction hierarchies.
- [DEV] Use a memory allocation for events to speed-up their executions.

### Changed

- [USER] The progress bars refresh only periodically, for improved speed and better ETA.

### Fixed

- [USER] Fix the progress bar of the within-day model.
- [USER] Better formatting for the mean number of virtual legs in the HTML report.
- [USER] Improve TCH speed when some edges are restricted by discarding them from the graph.
- [USER] Fix how the weights are computed for restricted edges.
- [USER] Deserialize `null` or `None` values in the travel-time functions' points as `Infinity`.
- [DEV] Fix how waiting times and road length are recorded so that expected travel times are more
  accurate.
- [DEV] Fix how the spillback indicator is computed and reset.
- [DEV] Add a margin when checking FIFO property to avoid false positive.
- [DEV] In the TCH algorithms, never stall the source and target nodes (this prevented finding the
  best path when the source or the target was the candidate node).
- [DEV] In the TCH algorithms, use a margin when checking if a node can be stalled to prevent
  incorrect stalling because of rounding errors.

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

[unreleased]: https://github.com/MetropolisTHEMA/Metrolib/compare/0.6.0...HEAD
[0.6.0]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.6.0
[0.5.2]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.5.2
[0.5.1]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.5.1
[0.5.0]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.5.0
[0.4.3]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.4.3
[0.4.2]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.4.2
[0.4.1]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.4.1
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
