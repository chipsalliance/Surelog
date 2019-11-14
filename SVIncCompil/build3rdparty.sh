#!/bin/bash
set -e
# Any subsequent(*) commands which fail will cause the shell script to exit immediately

#########################################################################
# Build flatbuffers
#########################################################################
./buildflatbuffer.sh

#########################################################################
# Build Antlr4.72 for Java and C++ 
#########################################################################
./buildantlr.sh
