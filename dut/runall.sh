#!/usr/bin/env bash
set -eu

make TOP=image
./image.py
make clean

make TOP=image_read
./image_read.py
make clean

make TOP=image_write
./image_write.py
make clean

make TOP=kernel
./kernel.py
make clean

