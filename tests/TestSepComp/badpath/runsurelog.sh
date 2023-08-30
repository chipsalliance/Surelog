#!/usr/bin/env bash
$1 -init
$1 ../pkg1.sv ../pkg2.sv -sepcomp 
$1 badtop.sv  ../../EvalFunc/dut.sv -sepcomp 
$1 -link -d cache

