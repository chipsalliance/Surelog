#!/bin/bash
echo "Test cache capabilities (rerun)"
rm -rf slpp*

time $1 *.v  -d 0 +incdir+.+.. +libext+.v -writepp -v jkff_udp.v -mt max -parse -fileunit -nostdout

time $1 *.v  -d 0 +incdir+.+.. +libext+.v -writepp -v jkff_udp.v -mt max -parse -fileunit

