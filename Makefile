release:
	rm -rf flatbuffers; rm -rf antlr4
	cd SVIncCompil; ./build3rdparty_mini.sh
	cd SVIncCompil; ./buildrelease.sh

debug:
	rm -rf flatbuffers; rm -rf antlr4
	cd SVIncCompil; ./build3rdparty.sh
	cd SVIncCompil; ./builddebug.sh

all:
	rm -rf flatbuffers; rm -rf antlr4
	cd SVIncCompil; ./build3rdparty.sh
	cd SVIncCompil; ./buildall.sh

test:
	cd SVIncCompil/Testcases; ./regression.tcl
