#!/bin/bash

sudo apt-get update
sudo apt install -y cmake clang clang-c++ libboost-dev libboost-system-dev \
    libboost-mpi-dev openmpi-common openmpi-bin subversion htop \
    python-subprocess32 libgmp-dev libomp-dev awscli

sudo update-alternatives --install /usr/bin/cc cc /usr/bin/clang 100
sudo update-alternatives --install /usr/bin/c++ c++ /usr/bin/clang++ 100

# aeval will be copied from local
# git clone -b rnd-parallel https://github.com/grigoryfedyukovich/aeval.git /home/ubuntu/aeval
mkdir /home/ubuntu/out &&
cd /home/ubuntu/aeval &&
rm -rf build &&
mkdir build &&
cd build &&
cmake .. &&
make &&
make
