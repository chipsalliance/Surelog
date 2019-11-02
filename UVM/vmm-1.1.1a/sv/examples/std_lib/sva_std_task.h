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


// Example 3-41 Use of SYNTHESIS Macro
`ifndef SYNTHESIS

  int error_count = 0;
`ifdef SVA_VMM_LOG_ON
  // Example 3-42 Instance of the message service class
  vmm_log log;
  initial #1 log = new(assert_name, $psprintf("%m"));
`endif
`endif

  task sva_checker_error;
    input bit [60*8-1:0] err_msg;
`ifndef SYNTHESIS
    begin
    `ifdef ASSERT_MAX_REPORT_ERROR
      error_count = error_count + 1;
      if (error_count <= `ASSERT_MAX_REPORT_ERROR) begin
    `endif

// Example 3-45 Assertion failure reporting
    `ifndef SVA_CHECKER_NO_MESSAGE
    `ifdef SVA_VMM_LOG_ON
		$display("SVA_CHECKER entered logging");
       `vmm_error(log, 
         $psprintf("SVA_CHECKER_ERROR : %s : %0s : severity %0d", 
                    msg, err_msg, severity_level));
    `else
         $display("SVA_CHECKER_ERROR : %s : %s : %0s : severity %0d : time %0t : %m",
          assert_name, msg, err_msg, severity_level, $time);
    `endif
    `ifdef ASSERT_MAX_REPORT_ERROR
      end
    `endif
    `endif
//      if (severity_level == 0) sva_checker_finish;
    end
`endif
  endtask

  task sva_checker_init_msg;
`ifndef SYNTHESIS
    begin
    `ifndef SVA_CHECKER_NO_MESSAGE
    `ifdef SVA_VMM_LOG_ON
//     `vmm_note(log, 
//        $psprintf("SVA_CHECKER_NOTE: Initialized : Severity: %0d, Category: %0d", 
//         severity_level, category));
    `else 
          $display("SVA_CHECKER_NOTE: %s initialized @ %m Severity: %0d, Category: %0d",
                    assert_name,severity_level, category);
    `endif
    `endif
    end
`endif
  endtask

  task sva_checker_warning_msg;
`ifndef SYNTHESIS
    input [60*8-1:0] warning_msg;
    begin
    `ifndef SVA_CHECKER_NO_MESSAGE
    `ifdef SVA_VMM_LOG_ON
//      `vmm_warning(log, 
//          $psprintf("SVA_CHECKER_WARNING: Severity: %0d, Category: %0d, %s", 
//                      severity_level, category, warning_msg));
    `else
        $display("SVA_CHECKER_WARNING: %s @ %m, Message: %s",
                  assert_name, warning_msg);
    `endif
    `endif
    end
`endif
  endtask

  task sva_checker_finish;
`ifndef SYNTHESIS
    begin
      #100 $finish; 
    end
`endif
  endtask

// Example 3-43 Issuing an initial checker identification message
`ifndef SYNTHESIS
`ifdef ASSERT_INIT_MSG
  initial sva_checker_init_msg;
`endif // ASSERT_INIT_MSG
`endif // SYNTHESIS

// Example 3-40 Reset selection
`ifdef ASSERT_GLOBAL_RESET
  wire not_resetting = (`ASSERT_GLOBAL_RESET != 1'b0);
`else
  wire not_resetting = (reset_n != 0);
`endif // ASSERT_GLOBAL_RESET
  wire resetting = !not_resetting;
