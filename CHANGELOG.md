# Changelog

Changes starting with tag [USER] are of interest to end-users.
Changes starting with tag [DEV] are of interest to developers only.

The tag [INPUT] indicates changes affecting the input files.
The tag [OUTPUT] indicates changes affecting the output files.

## [Unreleased]

### Added

- [INPUT] Allow edges to have time-varying bottleneck flows with `bottleneck_flows` and
  `bottleneck_times` variables.
- [DEV] Add GNU General Public License v3.

### Changed

- [INPUT] Arbitrary ids can be used for all input values (negative integers, strings).
- [DEV] Rename the repository from Metrolib to Metropolis-Core.
- [DEV] Update README.md.

## [1.1.0] - 2025-06-06

### Added

- [INPUT] The `alpha` parameter can be used to specify the value of time at the alternative or trip
  level (it has the same effect as the `travel_utility.one` or `total_travel_utility.one` variables,
  with an opposite sign).

### Changed

- [INPUT] The `AlphaBetaGamma` schedule utility type is deprecated. Use `Linear` instead.

### Fixed

- [INPUT] Road-network parameter `max_pending_duration` is now optional when `spillback` is
  disabled, as could be expected.
- [USER] Error messages where not shown if occurring before the loggers were initialized.
- [USER] Fix a bug when running `routing_cli` from the same directory where the parameters JSON file
  is located.
- [USER] Fix bugs when running a simulation without a road network.

### Removed

- [USER] Remove the nested parquet example.

## [1.0.0] - 2025-01-06

First stable release of METROPOLIS2!

## [1.0.0-7] - 2024-12-21

### Fixed

- [DEV] Revert to tauri `1.x` to fix installer issues on Windows.

## [1.0.0-6] - 2024-12-17

### Fixed

- [DEV] Fix duckscript bug in the release.
- [DEV] Fix bug with Tauri on MacOS.

## [1.0.0-5] - 2024-12-17

### Added

- [INPUT] The `"UpperBound"` speed-function type can be used to limit the maximum speed at which a
  vehicle can travel.
- [USER] The error messages are logged to the `log.txt` output file.

### Changed

- [USER] Improve the error message that is shown when some origin / destination nodes are not part
  of the road network.
- [INPUT] Default number of iterations (`max_iterations`) is 1 (it was 0).
- [OUTPUT] Update the terminology for `running_times.json` output file.
- [OUTPUT] Optimize file size of `report.html`.
- [DEV] Use `jemalloc` as allocator for improved performances on Linux systems.
- [DEV] Profile queries are not computed for origin-destination pairs with no departure-time choice.
- [DEV] Road-network skims are not computed when they are not needed (e.g., when all trips have a
  route given as input).
- [DEV] Do not compute search space for origin / destination nodes with few occurrences. A TCH query
  is run instead of Intersect query in this case.

### Fixed

- [OUTPUT] Fix the computation for expected travel time difference RMSE.
- [DEV] Fix a stack overflow that could happen when recursively running too many events.
- [DEV] Various improvements and bug fixes.

## [1.0.0-4] - 2024-03-15

### Changed

- [USER] The `compute_choices` executable is replaced by a `only_compute_decisions` parameter in the
  main executable.
- [USER] The `compute_travel_times` is renamed `routing_cli` and it is now able to road / write CSV
  and Parquet files.

### Fixed

- [DEV] Various fixes to make the GUI compile through Github Actions.

## [1.0.0-rc.3] - 2024-03-15

### Added

- [USER] Add back the GUI executable.

## [1.0.0-rc.2] - 2024-03-13

### Removed

- [USER] Temporarily remove the GUI executable as it fails to compile on Windows and MacOS.

## [1.0.0-rc.1] - 2024-03-13

### Added

- [USER] Prototype GUI for METROPOLIS2 with the binary `metropolis_gui`.
- [INPUT] The paths to the input files and the output directory are set in the parameters JSON file.
- [INPUT] Custom vehicle ids can be used (instead of vehicle indices numbered from 0 to n - 1).
- [INPUT] Add the `max_iterations` parameter in the simulation parameters to limit the number of
  iterations.

### Changed

- [USER] The command-line interface only takes the path to the parameters JSON file as argument.
- [INPUT] The population and network input files accept the Parquet and CSV format instead of JSON.
- [INPUT] The road-network conditions input file accept the Parquet and CSV format instead of JSON.
- [INPUT] The road-network parameters are no longer nested in the network parameters.
- [OUTPUT] Use more interesting variables in the report HTML file.
- [OUTPUT] Use the new terminology in the report HTML file.
- [OUTPUT] The road-network conditions output files are saved in Parquet or CSV format instead of
  JSON (according to `saving_format` parameter).

### Removed

- [INPUT] Stopping criteria can no longer be used in the parameters (use `max_iterations` parameter
  value instead).

## [0.8.0] - 2024-02-29

### Added

- [INPUT] Add the `ExponentialUnadjusted` learning model (exponential model with no adjustment for
  the first iteration).
- [INPUT] Add option to force the route to be taken for road legs (parameter `route` of a road leg).
- [INPUT] Add option to set the speed at which the holes / free space left by vehicles leaving a
  road propagate backward (road-network parameter `backward_wave_speed`, default is infinite speed).
- [INPUT] Add option to remove the inflow constraint on edges (road-network parameter
  `constrain_inflow`, default is to constrain both inflows and outflows).
- [OUTPUT] Add the root mean squared difference of departure time in the iteration results.
- [OUTPUT] Add the root mean squared difference between simulated and expected travel time in the
  iteration results.
- [OUTPUT] Add the simulated and expected road-network weights RMSE (root mean squared difference)
  in the iteration results.
- [OUTPUT] Add the length of the route that is new compared to the previous iteration in the
  leg-level results.
- [OUTPUT] Add the departure time shift compared to the previous iteration in the trip-level and
  leg-level results.
- [OUTPUT] Add a boolean indicator indicating if an agent shifted mode compared to the previous
  iteration.
- [USER] Add a warning when deserializing a road network with parallel edges.

### Changed

- [INPUT] For the `Exponential` learning model, the `alpha` value is no longer nested in a
  structure.
- [INPUT] Road edge's lane number can take non-integer values.
- [USER] For the `Exponential` learning model, the `alpha` value represents the weight of the
  simulated weights (previously, it was the expected weights).
- [USER] For speed-density functions, the travel time of a vehicle on an edge is based on the
  density before the vehicle enters the edge (i.e., not the density including the vehicle's own
  length as it was done previously).
- [USER] The departure-time stop criterion only considers the agents who did not switch to another
  mode (breaking change: the default value to use in case of mode switch is no longer required).
- [DEV] Run schemas generation with dev profile to reduce compile time.
- [DEV] Lints are configured directly in `Cargo.toml`, using Rust 1.74.0.
- [DEV] Road-network weights only store the weights of the edges which are accessible by the
  vehicle.

### Fixed

- [OUTPUT] Fix a crash when running `metropolis` with an output directory that does not exist.
- [OUTPUT] Fix number of decimals for road-network weights RMSE in the report HTML file.
- [DEV] Fix nodes being duplicated when a graph is deserialized.
- [DEV] Fix crash when using a uniform random value equal to 1.0.

### Removed

- [USER] The book and API documentation are not longer part of the released zipfile.

## [0.7.0] - 2023-11-16

### Changed

- [OUTPUT] The iteration results are saved in a single file, `iteration_results.ext`, updated at
  each iteration. Previously they were saved in a different file for each iteration. The filetype
  and extension are based on the `saving_format` parameter (`JSON`, `Parquet` or `CSV`).
- [USER] Congestion is set to zero when free-flow travel time is zero, as a convention. Previously,
  congestion was set to NaN.
- [DEV] Use `debug=false` for dependencies to decrease the binary size.

### Fixed

- [USER] A crash occurring for road legs with same origin as destination is fixed.

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
- [USER] When a vehicle is forced to be released on the next edge, it does not use any additional
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
- [INPUT] Add road-network parameter `algorithm_type` to choose the algorithm used for
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
  is now explicitly specified for either the origin or destination (or intermediary stop) making
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

[unreleased]: https://github.com/Metropolis2/Metropolis-Core/compare/1.1.0...HEAD
[1.0.0]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/1.1.0
[1.0.0]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/1.0.0
[1.0.0-7]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/1.0.0-7
[1.0.0-6]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/1.0.0-6
[1.0.0-5]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/1.0.0-5
[1.0.0-4]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/1.0.0-4
[1.0.0-rc.3]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/1.0.0-rc.3
[1.0.0-rc.2]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/1.0.0-rc.2
[1.0.0-rc.1]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/1.0.0-rc.1
[0.8.0]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/0.8.0
[0.7.0]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/0.7.0
[0.6.0]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/0.6.0
[0.5.2]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/0.5.2
[0.5.1]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/0.5.1
[0.5.0]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/0.5.0
[0.4.3]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/0.4.3
[0.4.2]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/0.4.2
[0.4.1]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/0.4.1
[0.4.0]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/0.4.0
[0.3.1]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/0.3.1
[0.3.0]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/0.3.0
[0.2.1]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/0.2.1
[0.2.0]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/0.2.0
[0.1.7]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/0.1.7
[0.1.6]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/0.1.6
[0.1.5]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/0.1.5
[0.1.4]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/0.1.4
[0.1.3]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/0.1.3
[0.1.2]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/0.1.2
[0.1.1]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/0.1.1
[0.1.0]: https://github.com/Metropolis2/Metropolis-Core/releases/tag/0.1.0
