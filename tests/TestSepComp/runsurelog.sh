#!/usr/bin/env bash
$1 -init
$1 pkg1.sv pkg2.sv -sepcomp 
$1 top.sv -sepcomp 
$1 -link -d uhdm -nobuiltin -d cache 

