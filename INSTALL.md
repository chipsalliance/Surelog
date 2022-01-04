# Surelog Install and Build Instructions

Executable: `surelog`

## Clone and Initialize Submodules

```
git clone https://github.com/alainmarcel/Surelog.git
cd Surelog
git submodule update --init --recursive
```

## Build Dependencies

* cmake >= 3.13
* python >= 3.6+
  * orderedmultidict
  * psutil (required to run regression tests)

### Ubuntu/Debian

`sudo apt-get install build-essential cmake git pkg-config tclsh swig uuid-dev libgoogle-perftools-dev python3 python3-dev default-jre lcov`

*Note:* If you intend to change the grammar, add: `sudo apt-get install ant`

*Note:* If you have a version of cmake before 3.13 on your system
(check with `cmake --version`), you need get a version that is more current.
On Debian-like systems (includes Ubuntu), that would be
```
wget -q -O- https://apt.kitware.com/keys/kitware-archive-latest.asc | sudo apt-key add -
sudo add-apt-repository 'deb https://apt.kitware.com/ubuntu/ xenial main'
sudo apt-get remove -y cmake
sudo apt-get install -y cmake
```


### Nix Package Manager

In a [nix environment](https://nixos.org) simply type `nix-shell` to set up the dependencies.


## Build Instructions

```
make
```

For debug builds:
```
make debug
```

As a guide where unit tests are not covering code yet (we're using [gtest]),
run

```
make coverage-build/html
```

This creates an HTML output allowing to drill down to each line indicating
if it was covered in a unit test.

Helping out here would be in particular useful to the project, as most code
is only covered by regression tests currently but not by targeted unittests
explicitly probing the correctness of the implemented functionality.

Installation:
```
make install
```

The installation path may be set by specifying a `PREFIX`. The default is `/usr/local`.
For example:
```
make install PREFIX=~/.local
```


  * or see [`src/README`](./src/README.md)

[gtest]: https://github.com/google/googletest
