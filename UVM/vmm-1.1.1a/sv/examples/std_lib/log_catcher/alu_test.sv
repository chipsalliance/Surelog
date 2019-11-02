//
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    Copyright 2009 Mentor Graphics Corporation
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


program alu_test(alu_if.drvprt alu_drv_port, alu_if.monprt alu_mon_port);

`include "alu_env.sv"

class err_catcher extends vmm_log_catcher;

  int num_errors = 0;
  int max_errors;

  function new(int max_errors);
    this.max_errors = max_errors;
  endfunction

  // Modifies the message and severity if num of errors is less than
  // maximum number of acceptable errors
  virtual function void caught(vmm_log_msg msg);
    if (num_errors < max_errors) begin
      msg.text[0] = {"ACCEPTABLE ERROR: ", msg.text[0]}; 
      msg.effective_severity = vmm_log::WARNING_SEV;
      issue(msg);
      num_errors++;
    end
    else begin
      `ifdef INTEROP_REGRESS
      // prevent errors
      msg.text.push_back("**** INTEROP_REGRESS is ON. This would be an error otherwise.");
      msg.effective_severity = vmm_log::WARNING_SEV;
      `endif // INTEROP_REGRESS
      throw(msg);
    end
  endfunction

endclass

alu_env env;
err_catcher ctcher;

initial begin
  env = new(alu_drv_port, alu_mon_port);
  ctcher = new(5); //Up to 5 errors are acceptable
  env.gen_cfg();
  env.cfg.num_scenarios = 50;
  env.build();
  void'(env.sb.log.catch(ctcher,
                   .severity(vmm_log::ERROR_SEV),
                   .text("/Mismatch/")));
  env.run();
end

endprogram


