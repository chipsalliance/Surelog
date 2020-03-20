# If you have runtime memory issues, disable tcmalloc: add -DNO_TCMALLOC to the make line

PREFIX?=/usr/local

release:
	mkdir -p build/tests;
	mkdir -p build/dist;
	mkdir -p dist;
	cd build; cmake ../ -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=$(PREFIX)
	$(MAKE) -C build

debug:
	mkdir -p dbuild/tests;
	mkdir -p dbuild/dist;
	mkdir -p dist;
	cd dbuild; cmake ../ -DCMAKE_BUILD_TYPE=Debug -DCMAKE_INSTALL_PREFIX=$(PREFIX)
	$(MAKE) -C dbuild

test/unittest:
	cd build && ctest

test/regression:
	mkdir -p build/tests;
	cd build; ../tests/regression.tcl mt=0 show_diff

test: test/unittest test/regression

clean:
	rm -rf dist;
	if [ -d build ] ; then $(MAKE) -C build clean ; fi
	rm -rf build

install:
	cd build; make install

test_install:
	cd tests/TestInstall ; rm -rf build; mkdir -p build; cd build; cmake ../ -DINSTALL_DIR=$(PREFIX); make ; ./test_hellosureworld --version

uninstall:
	rm -f  $(PREFIX)/bin/surelog
	rm -rf $(PREFIX)/lib/surelog
	rm -rf $(PREFIX)/include/surelog
