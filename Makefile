# Use bash as the default shell
SHELL := /usr/bin/env bash

ifdef $(LC_ALL)
	undefine LC_ALL
endif

UNAME := $(shell uname)
ifeq ($(UNAME), Linux)
NPROC = $(shell nproc)
endif
ifeq ($(UNAME), Darwin)
NPROC = $(shell sysctl -n hw.physicalcpu)
endif

ifeq ($(CPU_CORES),)
	CPU_CORES := $(NPROC)
	ifeq ($(CPU_CORES),)
		CPU_CORES := 2  # Good minimum assumption
	endif
endif

PREFIX ?= /usr/local
ADDITIONAL_CMAKE_OPTIONS ?=
export CTEST_PARALLEL_LEVEL = $(CPU_CORES)

release: run-cmake-release
	cmake --build build -j $(CPU_CORES)

release-shared: run-cmake-release-shared
	cmake --build build -j $(CPU_CORES)

release_with_python: run-cmake-release-with-python
	cmake --build build -j $(CPU_CORES)

release_no_tcmalloc: run-cmake-release_no_tcmalloc
	cmake --build build -j $(CPU_CORES)

debug: run-cmake-debug
	cmake --build dbuild -j $(CPU_CORES)

quick: run-cmake-quick
	cmake --build dbuild -j $(CPU_CORES)

run-cmake-release:
	cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=$(PREFIX) -DBUILD_SHARED_LIBS=OFF $(ADDITIONAL_CMAKE_OPTIONS) -S . -B build

run-cmake-release-shared:
	cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=$(PREFIX) -DBUILD_SHARED_LIBS=ON $(ADDITIONAL_CMAKE_OPTIONS) -S . -B build

run-cmake-release-with-python:
	cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=$(PREFIX) $(ADDITIONAL_CMAKE_OPTIONS) -DSURELOG_WITH_PYTHON=1 -DCMAKE_CXX_FLAGS=-fpermissive -S . -B build

run-cmake-release_no_tcmalloc:
	cmake -DSURELOG_WITH_TCMALLOC=Off -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=$(PREFIX) $(ADDITIONAL_CMAKE_OPTIONS) -S . -B build

run-cmake-debug:
	cmake -DCMAKE_BUILD_TYPE=Debug -DCMAKE_INSTALL_PREFIX=$(PREFIX) -DSURELOG_WITH_TCMALLOC=Off $(ADDITIONAL_CMAKE_OPTIONS) -S . -B dbuild

run-cmake-quick:
	cmake -DQUICK_COMP=1 -DCMAKE_BUILD_TYPE=Debug -DCMAKE_INSTALL_PREFIX=$(PREFIX) -DSURELOG_WITH_TCMALLOC=Off $(ADDITIONAL_CMAKE_OPTIONS) -S . -B dbuild

run-cmake-coverage:
	cmake -DCMAKE_BUILD_TYPE=Debug -DCMAKE_INSTALL_PREFIX=$(PREFIX) -DMY_CXX_WARNING_FLAGS="--coverage" $(ADDITIONAL_CMAKE_OPTIONS) -S . -B coverage-build

test/unittest: run-cmake-release
	cmake --build build --target UnitTests -j $(CPU_CORES)
	pushd build && ctest --output-on-failure && popd

test/unittest-d: run-cmake-debug
	cmake --build dbuild --target UnitTests -j $(CPU_CORES)
	pushd dbuild && ctest --output-on-failure && popd

test/unittest-coverage: run-cmake-coverage
	cmake --build coverage-build --target UnitTests -j $(CPU_CORES)
	pushd coverage-build && ctest --output-on-failure && popd

coverage-build/surelog.coverage: test/unittest-coverage
	lcov --no-external --exclude "*_test.cpp" --capture --directory coverage-build/CMakeFiles/surelog.dir --base-directory src --output-file coverage-build/surelog.coverage

coverage-build/html: coverage-build/surelog.coverage
	genhtml --output-directory coverage-build/html $^
	realpath coverage-build/html/index.html

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

# Formal equivalence checking of Surelog+UHDM+UHDMYosysPlugin+Yosys and Yosys parsers
verification: release
	cmake -E make_directory build/tests
	cmake -E remove_directory build/test
	cmake -E make_directory build/test
	tclsh tests/cmake_gen.tcl . build/test verification
	cmake -S build/test -B build/test/build
	pushd build && cmake --build test/build -j $(CPU_CORES) && popd
	pushd build && tclsh ../tests/regression.tcl diff_mode show_diff && popd

test/regression: release
	python3 scripts/regression.py run --jobs $(CPU_CORES) --show-diffs

test/valgrind: debug
	python3 scripts/regression.py run --tool valgrind --filters TypeParamElab --build-dirpath ${PWD}/dbuild
	python3 scripts/regression.py run --tool valgrind --filters ArianeElab --build-dirpath ${PWD}/dbuild
	python3 scripts/regression.py run --tool valgrind --filters ArianeElab2 --build-dirpath ${PWD}/dbuild
	python3 scripts/regression.py run --tool valgrind --filters BlackParrotMuteErrors --build-dirpath ${PWD}/dbuild

test: release test/unittest test/regression

clean:
	$(RM) -r build dbuild coverage-build dist tests/TestInstall/build

install: release
	cmake --install build

install-shared: release-shared
	cmake --install build

test_install:
	cmake -DCMAKE_BUILD_TYPE=Release -DINSTALL_DIR=$(PREFIX) -DCMAKE_PREFIX_PATH=$(PREFIX) $(ADDITIONAL_CMAKE_OPTIONS) -S tests/TestInstall -B tests/TestInstall/build
	cmake --build tests/TestInstall/build -j $(CPU_CORES)

# Using pkg-config. Its search-path might be set in different ways. Set both.
# Depends on `install`, but skip dependency allow testing separately. Do:
#    PREFIX=... make install test_install_pkgconfig
test_install_pkgconfig:
	PKG_CONFIG_PATH="$(PREFIX)/lib/pkgconfig:${PKG_CONFIG_PATH}" \
	PKG_CONFIG_PATH_FOR_TARGET="$(PREFIX)/lib/pkgconfig:${PKG_CONFIG_PATH_FOR_TARGET}" \
        $(MAKE) -f tests/TestInstall/Makefile \
            tests/TestInstall/build/hellosureworld \
            tests/TestInstall/build/hellouhdm \
            tests/TestInstall/build/hellodesign

uninstall:
	$(RM) -r $(PREFIX)/bin/surelog
	$(RM) -r $(PREFIX)/lib/libsurelog*
	$(RM) -r $(PREFIX)/include/Surelog
