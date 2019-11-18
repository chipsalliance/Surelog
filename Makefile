release:
	mkdir -p build/tests;
	mkdir -p dist;
	cd build; cmake ../ -DCMAKE_BUILD_TYPE=Release; make -j 4 
	cd build; ../tests/regression.tcl mt=0 show_diff

test:
	mkdir -p build/tests;
	cd build; ../tests/regression.tcl mt=0

clean:
	rm -rf build;
	chmod -fR u+rwx dist; rm -rf dist;

install:
	cd build; make install

