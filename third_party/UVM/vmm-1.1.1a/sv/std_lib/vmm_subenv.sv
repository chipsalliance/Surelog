// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    All Rights Reserved Worldwide
// 
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
// 
//        http://www.apache.org/licenses/LICENSE-2.0
// 
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
// 


function vmm_subenv::new(string         name,
                         string         inst,
                         `VMM_CONSENSUS end_test
                         `VMM_SUBENV_BASE_NEW_EXTERN_ARGS);
`ifdef VMM_SUBENV_BASE_NEW_CALL
   super.new(`VMM_SUBENV_BASE_NEW_CALL);
`endif
   this.log = new(name, inst);
   this.end_test = end_test;
endfunction: new


function string vmm_subenv::psdisplay(string prefix = "");
   $sformat(psdisplay, "%sSub-Environment %s(%s): ", prefix,
            this.log.get_name(), this.log.get_instance());
   return psdisplay;
endfunction


function vmm_consensus vmm_subenv::get_consensus();
   return this.end_test;
endfunction


function void vmm_subenv:: configured();
   this.state = CONFIGURED;
endfunction: configured


task vmm_subenv::start();
   if (this.state == NEWED) begin
      `vmm_error(this.log, "Sub-environment started before being configured");
   end
   this.state = STARTED;
endtask: start


task vmm_subenv::stop();
   if (this.state != STARTED) begin
      `vmm_warning(this.log, "Attempting to stop a sub-environment that has not been started");
   end
   this.state = STOPPED;
endtask: stop


task vmm_subenv::reset(vmm_env::restart_e kind = vmm_env::FIRM);
   this.state = STOPPED;
endtask: reset


task vmm_subenv::cleanup();
   if (this.state != STOPPED) begin
      `vmm_warning(this.log, "Attempting to clean-up a sub-environment that has not been stopped");
   end
   this.state = CLEANED;
endtask: cleanup
   

function void vmm_subenv::report();
endfunction: report


function string vmm_subenv::do_psdisplay(string prefix = "");
   this.__vmm_done_user = 0;
   return "";
endfunction


task vmm_subenv::do_vote();
   this.__vmm_done_user = 0;
endtask


task vmm_subenv::do_start();
   this.__vmm_done_user = 0;
endtask


task vmm_subenv::do_stop();
   this.__vmm_done_user = 0;
endtask


task vmm_subenv::do_reset(vmm_env::restart_e kind);
   this.__vmm_done_user = 0;
endtask
