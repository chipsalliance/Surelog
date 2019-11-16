##
## -------------------------------------------------------------
##    Copyright 2004-2008 Synopsys, Inc.
##    All Rights Reserved Worldwide
##
##    Licensed under the Apache License, Version 2.0 (the
##    "License"); you may not use this file except in
##    compliance with the License.  You may obtain a copy of
##    the License at
##
##        http://www.apache.org/licenses/LICENSE-2.0
##
##    Unless required by applicable law or agreed to in
##    writing, software distributed under the License is
##    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
##    CONDITIONS OF ANY KIND, either express or implied.  See
##    the License for the specific language governing
##    permissions and limitations under the License.
## -------------------------------------------------------------
##


OPTS	=

COMP_OPTS = -sverilog -ntb_opts dtm $(OPTS) \
	    +incdir+$(VMM_HOME)/sv+../verif+../tests

RUN_OPTS  =

TEST = Default

all default: clean comp run 

comp:
	vcs -sverilog $(COMP_OPTS) \
		../rtl/alu.v ../verif/alu_test.sv ../verif/alu_tb_top.sv

sep_comp: comp_pkg comp_tests comp_dut

comp_pkg:
	vlogan -sep_cmp -sverilog $(COMP_OPTS) ../verif/alu_if.sv
	vlogan -sep_cmp -sverilog $(COMP_OPTS) ../verif/alu_pkg.sv
	vcs -sep_cmp alu_pkg

comp_tests:
	vlogan -sep_cmp -sverilog $(COMP_OPTS) ../verif/alu_test.sv
	vcs -sep_cmp alu_test
	vcs -sep_cmp alu_test -ntb_opts genShellOnly

comp_dut:
	vcs -sep_cmp -sverilog -ntb_vl $(COMP_OPTS) \
		../rtl/alu.v ./alu_test.svshell ../verif/alu_tb_top.sv

run:
	./simv $(RUN_OPTS) +vmm_test=$(TEST)

sep_run:
	./simv $(RUN_OPTS) -sep_cmp=alu_test +vmm_test=$(TEST)

clean:
	rm -rf simv* csrc
	rm -rf vc_hdrs.h .vcsmx_rebuild *.log
	rm -rf work/* *.svshell

