<a id="readme-top"></a>
<!-- PROJECT SHIELDS -->
<!--
*** I'm using markdown "reference style" links for readability.
*** Reference links are enclosed in brackets [ ] instead of parentheses ( ).
*** See the bottom of this document for the declaration of the reference variables
*** for contributors-url, forks-url, etc. This is an optional, concise syntax you may use.
*** https://www.markdownguide.org/basic-syntax/#reference-style-links
-->
[![Contributors][contributors-shield]][contributors-url]
[![Forks][forks-shield]][forks-url]
[![Stargazers][stars-shield]][stars-url]
[![Issues][issues-shield]][issues-url]
[![GPL v3][license-shield]][license-url]
<!-- [![LinkedIn][linkedin-shield]][linkedin-url] -->



<!-- PROJECT LOGO -->
<br />
<div align="center">
  <a href="https://github.com/Metropolis2/Metropolis-Core">
    <img src="icons/80x80.png" alt="Logo" width="80" height="80">
  </a>

<h3 align="center">Metropolis-Core</h3>

  <p align="center">
      Metropolis-Core is the Rust-based core of the METROPOLIS2 simulator.
    <br />
    <a href="https://docs.metropolis2.org"><strong>Explore the docs »</strong></a>
    <br />
    <br />
    <a href="https://metropolis2.org">Website</a>
    &middot;
    <a href="https://github.com/Metropolis2/Metropolis-Core/issues/new?labels=bug&template=bug-report---.md">Report Bug</a>
    &middot;
    <a href="https://github.com/Metropolis2/Metropolis-Core/issues/new?labels=enhancement&template=feature-request---.md">Request Feature</a>
  </p>
</div>



<!-- TABLE OF CONTENTS -->
<details>
  <summary>Table of Contents</summary>
  <ol>
    <li>
      <a href="#about-the-project">About The Project</a>
      <ul>
        <li><a href="#built-with">Built With</a></li>
      </ul>
    </li>
    <li>
      <a href="#getting-started">Getting Started</a>
      <ul>
        <li><a href="#prerequisites">Prerequisites</a></li>
        <li><a href="#installation">Installation</a></li>
      </ul>
    </li>
    <li><a href="#usage">Usage</a></li>
    <li><a href="#roadmap">Roadmap</a></li>
    <li><a href="#contributing">Contributing</a></li>
    <li><a href="#license">License</a></li>
    <li><a href="#contact">Contact</a></li>
    <li><a href="#acknowledgments">Acknowledgments</a></li>
  </ol>
</details>



<!-- ABOUT THE PROJECT -->
## About The Project

[![METROPOLIS2 example output][product-screenshot]](https://metropolis2.org)

METROPOLIS2 is a dynamic multi-modal agent-based transport simulator.

<!-- TODO add graph of project structure -->

### Built With

[![Rust][Rust]][Rust-url]

Metropolis-Core make use of the [Rust standard library](https://doc.rust-lang.org/std/)
and some awesome Rust crates, including:

- [anyhow](https://crates.io/crates/anyhow) for error handling
- [arrow](https://crates.io/crates/arrow) / [parquet](https://crates.io/crates/parquet) for input /
  output operations
- [clap](https://crates.io/crates/clap) for command line interface
- [hashbrown](https://crates.io/crates/hashbrown) for hash collections
- [indicatif](https://crates.io/crates/indicatif) / [log](https://crates.io/crates/log) /
  [simplelog](https://crates.io/crates/simplelog) for logging and progress bar
- [num-traits](https://crates.io/crates/num-traits) for generic mathematics
- [petgraph](https://crates.io/crates/petgraph) for graphs
- [rayon](https://crates.io/crates/rayon) for parallelization

<p align="right">(<a href="#readme-top">back to top</a>)</p>



<!-- GETTING STARTED -->
## Getting Started

### Pre-built binaries

1. Go to the [Releases Tab](https://github.com/Metropolis2/Metropolis-Core/releases)
   and download the Zip file corresponding to your operating system
   (Windows, MacOS, or Linux).
2. Extract the Zip file in a folder.
3. The `metropolis cli` executable (or `metropolis_cli.exe` for Windows)
   is available in the `execs` directory. You can move it to any location or your choice.

### Compiling from source

1. Install Rust, either using the official
   [rustup installer](https://rust-lang.org/tools/install/)
   or any package manager you may use.
2. Clone this repository on your PC, you can use "git clone", if you have git
   installed, like this:

   ```shell
   git clone https://github.com/Metropolis2/Metropolis-Core.git
   ```

   Otherwise in the right up side of the repository page you will see a download
   button, download the repository as zip and extract it in a folder.

3. Open a new terminal in the folder you extracted the repository in.
4. Run this command in the terminal:

   ```shell
   cargo build --release -p metropolis-core
   ```

   This can take a few minutes depending on your system, but be patient.
5. The `metropolis cli` executable (or `metropolis_cli.exe` for Windows)
   is now available in the `target/release/` directory.

<p align="right">(<a href="#readme-top">back to top</a>)</p>



<!-- USAGE EXAMPLES -->
## Usage

Before running a METROPOLIS2 simulation with Metropolis-Core,
you first need to create the simulation input which
consists of a JSON file and multiple Parquet or CSV files.

Example input files are provided in the
[`examples/data/`](https://github.com/Metropolis2/Metropolis-Core/tree/main/core/examples/data)
directory, in CSV and Parquet version.
This files represent a simulation with no meaningful interpretation.
It makes use of all the possible input values so it is a great way to test if the simulator is
running properly.

Then, to run the simulation, open a terminal, locate the `metropolis_cli` executable and execute it
with (on Linux or MacOS):
```shell
./metropolis_cli [path_to_parameters.json]
```
or (on Windows):
```shell
.\metropolis_cli.exe [path_to_parameters.json]
```

_For more details, please refer to the [Documentation](https://docs.metropolis2.org)._

<p align="right">(<a href="#readme-top">back to top</a>)</p>


<!-- CITATION -->
## Citation

If you use this project in your research, please cite it as follows:

de Palma, A. & Javaudin, L. (2025). _METROPOLIS2_. [https://metropolis2.org](https://metropolis2.org)

Javaudin, L., & de Palma, A. (2024). _METROPOLIS2: Bridging theory and simulation in agent-based transport modeling._ Technical report, THEMA (THéorie Economique, Modélisation et Applications).

_Refer to [CITATION.cff](CITATION.cff) and [CITATION.bib](CITATION.bib) for details._


<!-- CONTRIBUTING -->
## Contributing

If you would like to add a feature to Metropolis-Core, start by opening an issue with the tag
"enhancement" so that we can discuss its feasibility.

If your suggestion is accepted, you can then create a Pull Request:

1. Fork the Project
2. Create your Feature Branch (`git checkout -b feature/AmazingFeature`)
3. Commit your Changes (`git commit -m 'Add some AmazingFeature'`)
4. Push to the Branch (`git push origin feature/AmazingFeature`)
5. Open a Pull Request

_For more details, please read [CONTRIBUTING.md](CONTRIBUTING.md)
and [CODE_OF_CONDUCT.md](CODE_OF_CONDUCT.md)._

<p align="right">(<a href="#readme-top">back to top</a>)</p>

## Semver

Metropolis-Core is following [Semantic Versioning 2.0](https://semver.org/).

Each new version is given a number MAJOR.MINOR.PATCH.
An increase of the MAJOR number indicates backward incompatibilities with previous versions.
An increase of the MINOR number indicates new features, that are backward-compatible.
An increase of the PATCH number indicates bug fixes.

<p align="right">(<a href="#readme-top">back to top</a>)</p>

<!-- ### Top contributors:

<a href="https://github.com/Metropolis2/Metropolis-Core/graphs/contributors">
  <img src="https://contrib.rocks/image?repo=Metropolis2/Metropolis-Core" alt="contrib.rocks image" />
</a>
-->



<!-- LICENSE -->
## License

Metropolis-Core is free and open-source software licensed under the
[GNU General Public License v3.0](https://www.gnu.org/licenses/).

You are free to:

- Modify and redistribute this software
- Use it for any purpose, personal or commercial

Under the following conditions:

- You retain the original copyright notice
- You distribute you modifications under the same license (GPL-3.0 or later)
- You document any significant changes you make

For the full license text and legal details, see the `LICENSE.txt` file.

<p align="right">(<a href="#readme-top">back to top</a>)</p>



<!-- CONTACT -->
## Contact

If you have any questions, either post an
[issue](https://github.com/Metropolis2/Metropolis-Core/issues)
or send an e-mail to any of these addresses:

- METROPOLIS2 team - contact@metropolis2.org
- Lucas Javaudin - metropolis@lucasjavaudin.com

Project Link: [https://github.com/Metropolis2/Metropolis-Core](https://github.com/Metropolis2/Metropolis-Core)

<p align="right">(<a href="#readme-top">back to top</a>)</p>



<!-- ACKNOWLEDGMENTS -->
## Acknowledgments

METROPOLIS2 took inspiration from the METROPOLIS (first of the name) simulator by André de Palma,
Fabrice Marchal and Yurii Nesterov.

<p align="right">(<a href="#readme-top">back to top</a>)</p>



<!-- MARKDOWN LINKS & IMAGES -->
<!-- https://www.markdownguide.org/basic-syntax/#reference-style-links -->
[contributors-shield]: https://img.shields.io/github/contributors/Metropolis2/Metropolis-Core.svg?style=for-the-badge
[contributors-url]: https://github.com/Metropolis2/Metropolis-Core/graphs/contributors
[forks-shield]: https://img.shields.io/github/forks/Metropolis2/Metropolis-Core.svg?style=for-the-badge
[forks-url]: https://github.com/Metropolis2/Metropolis-Core/network/members
[stars-shield]: https://img.shields.io/github/stars/Metropolis2/Metropolis-Core.svg?style=for-the-badge
[stars-url]: https://github.com/Metropolis2/Metropolis-Core/stargazers
[issues-shield]: https://img.shields.io/github/issues/Metropolis2/Metropolis-Core.svg?style=for-the-badge
[issues-url]: https://github.com/Metropolis2/Metropolis-Core/issues
[license-shield]: https://img.shields.io/github/license/Metropolis2/Metropolis-Core.svg?style=for-the-badge
[license-url]: https://github.com/Metropolis2/Metropolis-Core/blob/master/LICENSE.txt
[linkedin-shield]: https://img.shields.io/badge/-LinkedIn-black.svg?style=for-the-badge&logo=linkedin&colorB=555
[linkedin-url]: https://linkedin.com/in/lucas-javaudin
[product-screenshot]: images/traffic_flows.jpg
<!-- Shields.io badges. You can a comprehensive list with many more badges at: https://github.com/inttter/md-badges -->
[Rust]: https://img.shields.io/badge/Rust-%23000000.svg?style=for-the-badge&e&logo=rust&logoColor=white
[Rust-url]: https://rust-lang.org/
