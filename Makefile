# If you have runtime memory issues, disable tcmalloc: add -DNO_TCMALLOC to the make line

ifeq ($(CPU_CORES),)
CPU_CORES := $(shell nproc)
ifeq ($(CPU_CORES),)
CPU_CORES := 1
endif
endif

PREFIX ?= /usr/local

release: run-cmake-release
	cmake --build build

debug: run-cmake-debug
	cmake --build dbuild

run-cmake-release:
	mkdir -p build/tests dist
	cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=$(PREFIX) -S . -B build

run-cmake-debug:
	mkdir -p dbuild/tests dist
	cmake -DCMAKE_BUILD_TYPE=Debug -DCMAKE_INSTALL_PREFIX=$(PREFIX) -S . -B dbuild

test/unittest: run-cmake-release
	cmake --build build --target UnitTests
	pushd build; ctest --output-on-failure; popd

test/regression: run-cmake-release
	cd build; ../tests/regression.tcl mt=0 show_diff

test: test/unittest test/regression

test-parallel: release test/unittest
	mkdir -p build/tests
	rm -rf build/test; mkdir build/test
	tclsh tests/cmake_gen.tcl `pwd` `pwd`/build/test
	cmake -S build/test -B build/test/build
	pushd build; cmake --build test/build; popd
	pushd build; tclsh ../tests/regression.tcl diff_mode show_diff; popd

regression: release
	mkdir -p build/tests
	rm -rf build/test; mkdir build/test
	tclsh tests/cmake_gen.tcl `pwd` `pwd`/build/test
	cmake -S build/test -B build/test/build
	pushd build; cmake --build test/build; popd
	pushd build; tclsh ../tests/regression.tcl diff_mode show_diff; popd

clean:
	rm -rf build dist

install: release
	cmake --install build

test_install: release
	cmake -DCMAKE_BUILD_TYPE=Release -DINSTALL_DIR=`readlink -f ${PREFIX}` -S tests/TestInstall -B tests/TestInstall/build
	cmake --build tests/TestInstall/build

uninstall:
	rm -f  $(PREFIX)/bin/surelog
	rm -rf $(PREFIX)/lib/surelog
	rm -rf $(PREFIX)/include/surelog
