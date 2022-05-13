#!/bin/sh
sudo docker run --rm --user "$(id -u)":"$(id -g)" -v "$PWD":/usr/src/metrolib:z -w /usr/src/metrolib rust:1.60-bullseye cargo build --release
