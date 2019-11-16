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

VCS	= vcs -sverilog -ntb_opts dtm \
	      +incdir+$(VMM_HOME)/sv 

all: test

test: comp normal record playback

comp:
	$(VCS) $(OPTS) test.sv

normal:
	./simv +vmm_opts+NUM_TRANS=3+NUM_CHANS=1 +vmm_MODE=NORMAL \
		-l simv_tr=3_ch=1.log

record:
	./simv +vmm_opts+NUM_TRANS=10+NUM_CHANS=2 +vmm_MODE=RECORD \
		-l simv_tr=10_ch=2_rec.log

playback:
	./simv +vmm_opts+NUM_TRANS=10+NUM_CHANS=2 +vmm_MODE=PLAYBACK \
		-l simv_tr=10_ch=2_pbk.log

clean:
	rm -rf simv* csrc vc_hdrs.h .vcsmx_rebuild *.log *.dat \
		 work/* *.svshell *~

