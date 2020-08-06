# If you have runtime memory issues, disable tcmalloc: add -DNO_TCMALLOC to the make line

ifeq ($(CPU_CORES),)
  CPU_CORES := $(shell nproc)
  ifeq ($(CPU_CORES),)
    CPU_CORES := 1
  endif
endif

PREFIX?=../publish

release: run-cmake-release
	$(MAKE) -C build

debug: run-cmake-debug
	$(MAKE) -C dbuild

run-cmake-release:
	mkdir -p build/tests build/dist dist
	cd build; cmake ../ -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=$(PREFIX)/release

run-cmake-debug:
	mkdir -p dbuild/tests dbuild/dist dist
	cd dbuild; cmake ../ -DCMAKE_BUILD_TYPE=Debug -DCMAKE_INSTALL_PREFIX=$(PREFIX)/debug

test/unittest: run-cmake-release
	$(MAKE) -C build UnitTests
	cd build && ctest --output-on-failure

test/regression: run-cmake-release
	cd build; ../tests/regression.tcl mt=0 show_diff

test: test/unittest test/regression

test-parallel: release test/unittest
	mkdir -p build/tests; cd build; rm -rf test; mkdir test; cd test; ../../tests/cmake_gen.tcl; cmake .; time make -j $(CPU_CORES); cd ..; ../tests/regression.tcl diff_mode show_diff;

regression: release
	mkdir -p build/tests; cd build; rm -rf test; mkdir test; cd test; ../../tests/cmake_gen.tcl; cmake .; time make -j $(CPU_CORES); cd ..; ../tests/regression.tcl diff_mode show_diff;

clean:
	rm -rf build dist

install_debug: debug
	$(MAKE) -C build install_debug

install_release: release
	$(MAKE) -C build install_release

test_install: release
	cd tests/TestInstall ; rm -rf build; mkdir -p build; cd build; cmake ../ -DINSTALL_DIR=$(PREFIX); make ; ./test_hellosureworld --version

uninstall:
	rm -f  $(PREFIX)/bin/surelog
	rm -rf $(PREFIX)/lib/surelog
	rm -rf $(PREFIX)/include/surelog
