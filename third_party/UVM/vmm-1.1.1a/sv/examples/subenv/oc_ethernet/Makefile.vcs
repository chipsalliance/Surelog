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


VMM	= $(VMM_HOME)/sv
#VMM	= $(VCS_HOME)/etc/vmm

ETH	= ethernet
WB	= $(VMM_HOME)/sv/examples/std_lib/wishbone

DUT	= $(VMM_HOME)/shared/examples/oc_ethernet/rtl

VCS	=  vcs -R +plusarg_save -sverilog +incdir+$(VMM) -ntb_opts dtm \
	       +verilog1995ext+.v \
               +warn=noBCNACMBP +incdir+$(ETH)+$(WB)+$(DUT) $(OPTS) \
	       +define+SOLVER_WEIRDNESS \
	       -F $(DUT)/rtl_file_list.lst

all: blk_tx sys_tx

blk_trivial_test blk_tx: ral_oc_ethernet.sv
	$(VCS) blk_trivial_test.sv

ral_oc_ethernet.sv: oc_ethernet.ralf
	$(VMM_HOME)/shared/bin/ralgen -l sv -t oc_ethernet oc_ethernet.ralf

sys_trivial_test sys_tx: ral_dual_eth.sv
	$(VCS) dual_eth.v sys_trivial_test.sv

ral_dual_eth.sv: oc_ethernet.ralf dual_eth.ralf
	ralgen -l sv -t dual_eth dual_eth.ralf

clean:
	rm -rf ral_*.sv csrc simv* vc_hdrs.h *~
