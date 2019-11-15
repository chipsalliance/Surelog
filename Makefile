release:
	cd src; ./buildrelease.sh

test:
	cd src/Testcases; ./regression.tcl

clean:
	rm -rf flatbuffers;
	rm -rf antlr4;
	rm -rf src/build;
	rm -rf src/dist;
