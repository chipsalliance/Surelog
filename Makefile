release:
	cd SVIncCompil; ./build3rdparty_mini.sh
	cd SVIncCompil; ./buildrelease.sh

debug:
	cd SVIncCompil; ./build3rdparty.sh
	cd SVIncCompil; ./builddebug.sh

all:
	cd SVIncCompil; ./build3rdparty.sh
	cd SVIncCompil; ./buildall.sh

test:
	cd SVIncCompil/Testcases; ./regression.tcl


clean:
	rm -rf flatbuffers;
	rm -rf antlr4;
	rm -rf SVIncCompil/build;
	rm -rf SVIncCompil/dist;
