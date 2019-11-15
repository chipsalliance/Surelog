#!/bin/bash

yosys -o yosys.blif ../run_script.ys
cp yosys.blif yosys.log
