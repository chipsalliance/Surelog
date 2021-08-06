# Surelog Install instructions

Executable: `surelog`

# Development Environment Required

* Linux (Ubuntu or Centos)

* Unlimit all limits, in your .cshrc or .bashrc put "ulimit -s"
  that will enable gcc to compile the very large Antlr generated C++ files

* Please install the following package updates:

   * `sudo apt-get install build-essential cmake git pkg-config tclsh swig uuid-dev libgoogle-perftools-dev python3 python3-dev`

   * If you don't intend to change the grammar: `sudo apt-get install default-jre`

   * If you do intend to change the grammar: `sudo apt-get install default-jdk ant`

   * In a [nix environment](https://nixos.org) simply type `nix-shell` to set up the dependencies.

* If you have a version of cmake before 3.13 on your system
  (check with `cmake --version`), you need get a version that is more current.
  On Debian-like systems (includes Ubuntu), that would be
  ```
  wget -q -O- https://apt.kitware.com/keys/kitware-archive-latest.asc | sudo apt-key add -
  sudo add-apt-repository 'deb https://apt.kitware.com/ubuntu/ xenial main'
  sudo apt-get remove -y cmake
  sudo apt-get install -y cmake
  ```

* Download the Surelog source code
  ```
  git clone https://github.com/alainmarcel/Surelog.git
  cd Surelog
  git submodule update --init --recursive
  ```

* Build
  * `make`
  * `make debug`
  * make install (/usr/local/bin and /usr/local/lib/surelog by default, use PREFIX=<path> for alternative locations)
  * or see [`src/README`](./src/README.md)
