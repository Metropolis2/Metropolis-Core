# Changelog

## [Unreleased]

### Added

- The simulation can be run with other initial weights than free flow, with the new `--weights`
  command line argument.
- The initial iteration counter to use for the simulation can be specified in the parameters of the
  simulation (variable `init_iteration_counter`).
- Add arrival-times distribution for the last iteration in the HTML report.
- Add `CHANGELOG.md` to release zips.

### Modified

- Completed the example so that it include all possible input formats.
- Rename attribute `length` of a vehicle to `headway` for clarity (`length` is set as an alias for
  backward compatibility).

### Fixed

- Deserialize `null` values for constant travel-time functions as `Infinity`, consistently with how
  the such values are serialized.

## [0.1.7] - 2023-01-05

### Modify

- When generating JSON schemas, output directory is automatically created if it does not exist.

## [0.1.6] - 2023-01-05

### Added

- Allowed / restricted edges can be specified for each vehicle type through fields `allowed_edges`
  and `restricted_edges`.

### Modified

- In the pre-processing of the road network, a set of unique vehicle types is computed (two vehicle
  types are considered identical if they can share the same network weights and skims, i.e., they
  have the same speed function, allowed edges and restricted edges).
- Road network weights and skims are stored and computed for each _unique_ vehicle type
  (previously, this was done for each vehicle type).
- Some tweaks were done for `cargo-make` (e.g., no verbose output, Clippy by default).

### Fixed

- Various fixes for GitHub Actions.
- Fix `EdgeIndex` not properly document in the JSON Schemas.

## [0.1.5] - 2022-12-21

### Added

- The Changelog is automatically added to the GitHub releases.

### Changed

- Do not compile all features by default with `cargo-make`.

### Fixed

- Fix compiling with `cargo-make` on Windows and MacOS.
- Fix links to releases in the Changelog.

## [0.1.4] - 2022-12-20

### Added

- Add `Makefile.toml` to control the behavior of `cargo-make`.
- Add this changelog.
- Add README file.

## [0.1.3] - 2022-12-20

### Fixed

- Install `cargo-make` during the `publish` workflow.

## [0.1.2] - 2022-12-20

### Fixed

- Fix the filter used to detect tags of new releases.

## [0.1.1] - 2022-12-20

### Added

- Use `cargo-make` and GitHub Actions to automate building, testing and releasing new versions.

### Changed

- New format for logs.
- Default log level is INFO for logs to stdout and DEBUG for logs to file.
- Do not output source code in the documentation.

### Fixed

- Feature Jemalloc is disabled for Windows.
- Fix License filename.

### Security

- Remove `chrono` dependency that depends on a vulnerable version of `time`.

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
