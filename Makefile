all:
	rm -rf ccache; rm -rf flatbuffers; rm -rf python3.6; rm -rf antlr4
	cd SVIncCompil; ./build3rdparty_mini.sh
	cd SVIncCompil; ./buildrelease.sh
