#!/bin/bash
echo "Test cache capabilities (rerun)"
rm -rf test_cache/slpp*

time $1 --Mdir test_cache another_arbiter.v dff.v encoder.v m_input_mult.v synfifo.v uart.v arbiter_tb.v encoder_case.v full_adder.v lfsr_task.v mux21.v top.v +incdir+. +libext+.v -v jkff_udp.v -parse -fileunit -timescale=1ps/1ps -nostdout

time $1 --Mdir test_cache another_arbiter.v dff.v encoder.v m_input_mult.v synfifo.v uart.v arbiter_tb.v encoder_case.v full_adder.v lfsr_task.v mux21.v top.v +incdir+. +libext+.v -v jkff_udp.v -parse -fileunit -timescale=1ps/1ps

