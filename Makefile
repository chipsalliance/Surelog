# Use bash as the default shell
SHELL := /bin/bash

ifdef $(LC_ALL)
	undefine LC_ALL
endif

ifeq ($(CPU_CORES),)
	CPU_CORES := $(shell nproc)
	ifeq ($(CPU_CORES),)
		CPU_CORES := $(shell sysctl -n hw.physicalcpu)
	endif
	ifeq ($(CPU_CORES),)
		CPU_CORES := 2  # Good minimum assumption
	endif
endif

PREFIX ?= /usr/local
ADDITIONAL_CMAKE_OPTIONS ?=

# If 'on', then the progress messages are printed. If 'off', makes it easier
# to detect actual warnings and errors  in the build output.
RULE_MESSAGES ?= on

release: run-cmake-release
	cmake --build build -j $(CPU_CORES)

release_no_tcmalloc: run-cmake-release_no_tcmalloc
	cmake --build build -j $(CPU_CORES)

debug: run-cmake-debug
	cmake --build dbuild -j $(CPU_CORES)

run-cmake-release:
	cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=$(PREFIX) -DCMAKE_RULE_MESSAGES=$(RULE_MESSAGES) $(ADDITIONAL_CMAKE_OPTIONS) -S . -B build

run-cmake-release_no_tcmalloc:
	cmake -DNO_TCMALLOC=On -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=$(PREFIX) -DCMAKE_RULE_MESSAGES=$(RULE_MESSAGES) $(ADDITIONAL_CMAKE_OPTIONS) -S . -B build

run-cmake-debug:
	cmake -DCMAKE_BUILD_TYPE=Debug -DCMAKE_INSTALL_PREFIX=$(PREFIX) -DCMAKE_RULE_MESSAGES=$(RULE_MESSAGES) -DNO_TCMALLOC=On $(ADDITIONAL_CMAKE_OPTIONS) -S . -B dbuild

run-cmake-coverage:
	cmake -DCMAKE_BUILD_TYPE=Debug -DCMAKE_INSTALL_PREFIX=$(PREFIX) -DCMAKE_RULE_MESSAGES=$(RULE_MESSAGES) -DMY_CXX_WARNING_FLAGS="--coverage" $(ADDITIONAL_CMAKE_OPTIONS) -S . -B coverage-build

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

test/regression: run-cmake-release
	cd build && ../tests/regression.tcl mt=0 show_diff

test/valgrind: debug
	cd dbuild && ../tests/regression.tcl debug=valgrind test=TypeParamElab path=${PWD}/dbuild/bin
	cd dbuild && ../tests/regression.tcl debug=valgrind test=ArianeElab path=${PWD}/dbuild/bin

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

pytest/regression: release
	python3 scripts/regression.py run --jobs $(CPU_CORES) --show-diffs

pytest/valgrind: debug
	python3 scripts/regression.py run --tool valgrind --filters TypeParamElab --build-dirpath ${PWD}/dbuild
	python3 scripts/regression.py run --tool valgrind --filters ArianeElab --build-dirpath ${PWD}/dbuild

pytest: release test/unittest pytest/regression

clean:
	$(RM) -r build dbuild coverage-build dist tests/TestInstall/build
	# Only here for a short while until everyone who has checked out
	# the sources cleans the old codegen locations.
	$(RM) src/SourceCompile/VObjectTypes.h \
              src/SourceCompile/VObjectTypes.cpp \
              src/API/vobjecttypes_py.h \
              src/SourceCompile/SV3_1aTreeShapeListener.h \
              src/SourceCompile/SV3_1aPpTreeShapeListener.h
	$(RM) src/API/SV3_1aPythonListener.h \
              src/API/slSV3_1aPythonListener.py \
              src/API/slapi_wrap.cxx \
              src/API/slapi_scripts.h \
              src/API/slapi.py
	$(RM) src/Cache/header_generated.h \
              src/Cache/parser_generated.h \
              src/Cache/preproc_generated.h \
              src/Cache/python_api_generated.h

install: release
	cmake --install build

test_install:
	cmake -DCMAKE_BUILD_TYPE=Release -DINSTALL_DIR=$(PREFIX) -S tests/TestInstall -B tests/TestInstall/build
	cmake --build tests/TestInstall/build -j $(CPU_CORES)

uninstall:
	$(RM) -r $(PREFIX)/bin/surelog
	$(RM) -r $(PREFIX)/lib/surelog
	$(RM) -r $(PREFIX)/include/surelog
