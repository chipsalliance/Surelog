# If you have runtime memory issues, disable tcmalloc: add -DNO_TCMALLOC to the make line

# Use bash as the default shell
SHELL := /bin/bash

ifeq ($(CPU_CORES),)
	CPU_CORES := $(shell nproc)
	ifeq ($(CPU_CORES),)
		CPU_CORES := 1
	endif
endif

PREFIX ?= /usr/local

release: run-cmake-release
	cmake --build build -j $(CPU_CORES)

debug: run-cmake-debug
	cmake --build dbuild -j $(CPU_CORES)

run-cmake-release:
	cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=$(PREFIX) -S . -B build

run-cmake-debug:
	cmake -DCMAKE_BUILD_TYPE=Debug -DCMAKE_INSTALL_PREFIX=$(PREFIX) -S . -B dbuild

test/unittest: run-cmake-release
	cmake --build build --target UnitTests -j $(CPU_CORES)
	pushd build && ctest --output-on-failure && popd

test/regression: run-cmake-release
	cd build && ../tests/regression.tcl mt=0 show_diff

test: test/unittest test/regression

test-parallel: release test/unittest
	cmake -E make_directory build/tests
	cmake -E remove_directory build/test
	cmake -E make_directory build/test
	tclsh tests/cmake_gen.tcl . build/test
	cmake -S build/test -B build/test/build
	pushd build && cmake --build test/build -j $(CPU_CORES) && popd
	pushd build && tclsh ../tests/regression.tcl diff_mode show_diff && popd

hellodesign: release
	pushd build && tclsh ../tests/regression.tcl exe_name=hellodesign test=Inverter && popd

regression: release
	cmake -E make_directory build/tests
	cmake -E remove_directory build/test
	cmake -E make_directory build/test
	tclsh tests/cmake_gen.tcl . build/test
	cmake -S build/test -B build/test/build
	pushd build && cmake --build test/build -j $(CPU_CORES) && popd
	pushd build && tclsh ../tests/regression.tcl diff_mode show_diff && popd

clean:
	$(RM) -r build dist

install: release
	cmake --install build

test_install: release
	cmake -DCMAKE_BUILD_TYPE=Release -DINSTALL_DIR=$(PREFIX) -S tests/TestInstall -B tests/TestInstall/build
	cmake --build tests/TestInstall/build -j $(CPU_CORES)

uninstall:
	$(RM) -r $(PREFIX)/bin/surelog
	$(RM) -r $(PREFIX)/lib/surelog
	$(RM) -r $(PREFIX)/include/surelog
