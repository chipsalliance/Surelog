#!/usr/bin/env bash
rm -rf slpp_unit
$1 pkg1.sv -fileunit -parse -noelab -nouhdm -nobuiltin -nocomp -nohash -d cache
$1 pkg2.sv -fileunit -parse -noelab -nouhdm -nobuiltin -nocomp -nohash -d cache
$1 pkg1.sv pkg2.sv -fileunit -nohash -parse -d uhdm -nobuiltin -d cache
