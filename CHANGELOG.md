# Changelog

## [Unreleased]

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

[unreleased]: https://github.com/MetropolisTHEMA/Metrolib/compare/v0.1.4...HEAD
[0.1.4]: https://github.com/MetropolisTHEMA/Metrolib/releases/tag/v0.1.4
