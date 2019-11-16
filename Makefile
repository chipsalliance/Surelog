release:
	mkdir -p build;
	mkdir -p src/dist;
	cd build; cmake ../; make -j 4
	cd src; ./release.tcl "release tcmalloc"
	cd src/Testcases; ./regression.tcl

test:
	cd src/Testcases; ./regression.tcl

clean:
	rm -rf build;
	chmod -fR u+rwx src/dist; rm -rf src/dist;
