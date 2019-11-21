release:
	mkdir -p build/tests;
	mkdir -p build/dist;
	mkdir -p dist;
	cd build; cmake ../ -DCMAKE_BUILD_TYPE=Release
	$(MAKE) -C build
	cd build; ../tests/regression.tcl mt=0 show_diff
debug:
	mkdir -p dbuild/tests;
	mkdir -p dbuild/dist;
	mkdir -p dist;
	cd dbuild; cmake ../ -DCMAKE_BUILD_TYPE=Debug
	$(MAKE) -C dbuild


test:
	mkdir -p build/tests;
	cd build; ../tests/regression.tcl mt=0

clean:
	rm -rf dist;
	$(MAKE) -C build clean
	rm -rf build

install:
	cd build; make install

uninstall:
	rm -f  /usr/local/bin/surelog
	rm -rf /usr/local/lib/surelog
