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


VMM	= +incdir+$(VMM_HOME)/sv
#VMM	= -ntb_opts rvm

OPTS	= 

VCS	= vcs -R -sverilog +verilog1995ext+.v $(VMM) \
              -ntb_opts dtm +warn=noBCNACMBP 

all: test_frame test_mii test_mac
no_sva: test_frame test_mii_no_sva test_mac_no_sva


test_frame:
	$(VCS) $(OPTS) test_frame.sv

test_mii:
	$(VCS) $(OPTS)  test_mii.sv top.sv  \
                +incdir+.. +define+ASSERT_ON+SVA_CHECKERS+COVER_ON+ASSERT_INIT_MSG+SVA_CHECKER -assert quiet+report

test_mii_no_sva:
	$(VCS) $(OPTS) test_mii.sv top.sv

test_mac:
	$(VCS) $(OPTS)  test_mac.sv top.sv \
                +incdir+.. +define+ASSERT_ON+SVA_CHECKERS+COVER_ON+ASSERT_INIT_MSG+SVA_CHECKER -assert quiet+report

test_mac_no_sva:
	$(VCS) $(OPTS) test_mac.sv top.sv

clean:
	rm -rf simv* csrc *~ *.log vc_*.h *.vpd *.key *.db *.report .v*
