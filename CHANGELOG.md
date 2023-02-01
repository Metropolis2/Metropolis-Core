# Changelog

Changes starting with tag [USER] are of interest to end-users.
Changes starting with tag [DEV] are of interest to developers only.

The tag [INPUT] indicates changes affecting the input files.
The tag [OUTPUT] indicates changes affecting the output files.

## [Unreleased]

### Added

- [INPUT] New mode: `FixedTTF`. This mode is useful for modes without congestion (or with exogenous
  congestion), when the travel-time function between the start and end points are known. The
  departure time of a trip with this mode can be exogenous or endogenous. The trip can be composed
  of multiple legs (with optionnaly, different travel and schedule utility for each leg).
- [INPUT] For `Road` mode, the schedule utility can now be specified with parameters
  `origin_schedule_utility` and `destination_schedule_utility`. Previously, the schedule utility was
  specified at the agent level, with parameter `schedule_utility`.
- [USER] The simulation can be run with other initial weights than free flow, with the new
  `--weights` command line argument.
- [INPUT] The initial iteration counter to use for the simulation can be specified in the
  parameters of the simulation (variable `init_iteration_counter`).
- [INPUT] New type for the field `utility_model` for road modes: `Polynomial`, which takes as
  values degree 0, 1, 2, 3 and 4 coefficients of a polynomial function (constant, linear, quadratic
  and cubic functions are special cases of the `Polynomial` type).
- [OUTPUT] Add arrival-times distribution for the last iteration in the HTML report.
- [USER] Add `CHANGELOG.md` to release zips.
- [USER] Add tags [USER] and [DEV] in the Changelog to specify the concerned individuals (end-users
- [USER] Add tags [INPUT] and [OUTPUT] in the Changelog to indicate that input or output files are
  affected.
- [USER] Add JSON Schemas for the `compute_travel_times` script in the directory `schemas/tch/`.
- [USER] Add `book` directory with a documentation for Metropolis (in progress).
- [DEV] Add a way not to simplify a `PwlXYF` when building it so that all breakpoints are kept.
- [DEV] Add functions `constrain_to_domain`, `add_x_breakpoints`, `add_z_breakpoints`,
  `into_points`, `into_xs_and_ys` and `iter_eval` to `PwlXYF`.

### Changed

- [INPUT] [OUTPUT] The list of points for the piecewise-linear functions is serialized /
  deserialized as an array of arrays `[x, y]` (previously, it was an array of objects with keys `x`
  and `y`).
- [OUTPUT] The route taken by the agent (in the agent results) is serialized as an array of arrays
  `[e, t]`, where `e` is the edge index and `t` is the entry time on the edge (previously it was an
  array of objects with keys `edge` and `edge_entry`).
- [USER] Complete the example so that it include all possible input formats.
- [INPUT] Rename attribute `utility_model` of `Road` mode to `travel_utility` for clarity
  (`utility_model` is set as an alias for backward compatibility).
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
- [DEV] Rename `XYF` function `middle_departure_time` to `middle_x` to be consistent with the
  terminology for the `XYF` functions.

### Removed

- [INPUT] Parameters `schedule_utility` for an Agent is removed. The schedule utility is now
  specified at the mode-level.
- [Input] The parameter `desired_arrival` for `AlphaBetaGammaModel` is removed. The schedule utility
  is now explicitely specified for either the origin or destination (or intermediary stop) making
  this parameter useless.

### Deprecated

- [INPUT] The types `None`, `Proportional` and `Quadratic` for field `utility_model` raise a
  deprecated warning when used.

### Fixed

- [USER] Deserialize `null` values for constant travel-time functions as `Infinity`, consistently
  with how the such values are serialized.
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

[unreleased]: https://github.com/MetropolisTHEMA/Metrolib/compare/0.1.7...HEAD
[0.1.7]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.1.7
[0.1.6]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.1.6
[0.1.5]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.1.5
[0.1.4]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.1.4
[0.1.3]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.1.3
[0.1.2]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.1.2
[0.1.1]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.1.1
[0.1.0]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/0.1.0
