#!/bin/bash
set -e
sudo apt-get -y install eatmydata
sudo eatmydata apt-get -y install gcc python g++ pkg-config \
libz-dev libglib2.0-dev libpixman-1-dev libfdt-dev git
