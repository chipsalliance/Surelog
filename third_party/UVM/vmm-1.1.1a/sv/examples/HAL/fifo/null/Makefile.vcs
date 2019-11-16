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


SHARED	= ../../../../../shared/examples/syn_tb_fifo

all: shared test


shared:
	ln -s $(SHARED) shared


ENV	= ../tb_env.sv
ENV_OPTS= -sverilog +incdir+$(VMM_HOME)/sv \
	  +incdir+..+shared

OPTS	=
VCS	= vcs $(OPTS) -ntb_opts dtm +define+VMM_HW_ARCH_NULL


test: simv
	simv +vmm_log_default=debug

simv:
	$(VCS) ../test.sv $(ENV_OPTS) $(ENV)

clean:
	rm -rf *~ *.vro simv* csrc* *.vshell depchk*vr \
	       .__snps* *.db* *.vpd* *.log *~ obj scs* work \
		._Vera* *.cfg vc*.h *.key shared *.dump
