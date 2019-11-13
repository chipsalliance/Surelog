release_full:
	rm -rf ccache; rm -rf flatbuffers; rm -rf python3.6; rm -rf antlr4
	cd SVIncCompil; ./build3rdparty.sh
	cd SVIncCompil; ./buildrelease.sh

all:
	rm -rf ccache; rm -rf flatbuffers; rm -rf python3.6; rm -rf antlr4
	cd SVIncCompil; ./build3rdparty.sh
	cd SVIncCompil; ./buildall.sh

release:
	rm -rf ccache; rm -rf flatbuffers; rm -rf python3.6; rm -rf antlr4
	cd SVIncCompil; ./build3rdparty_mini.sh
	cd SVIncCompil; ./buildrelease.sh

test:
	cd SVIncCompil/Testcases; ./regression.tcl

debug:
	rm -rf ccache; rm -rf flatbuffers; rm -rf python3.6; rm -rf antlr4
	cd SVIncCompil; ./build3rdparty.sh
	cd SVIncCompil; ./builddebug.sh
