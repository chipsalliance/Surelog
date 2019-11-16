//###############################################################
//
//  Licensed to the Apache Software Foundation (ASF) under one
//  or more contributor license agreements.  See the NOTICE file
//  distributed with this work for additional information
//  regarding copyright ownership.  The ASF licenses this file
//  to you under the Apache License, Version 2.0 (the
//  "License"); you may not use this file except in compliance
//  with the License.  You may obtain a copy of the License at
//
//  http://www.apache.org/licenses/LICENSE-2.0
//
//  Unless required by applicable law or agreed to in writing,
//  software distributed under the License is distributed on an
//  "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
//  KIND, either express or implied.  See the License for the
//  specific language governing permissions and limitations
//  under the License.
//
//###############################################################


/*
  Assertion Macros
*/
`ifndef FAIL_IF
`define FAIL_IF(exp) \
  if (svunit_pkg::current_tc.fail(`"fail_if`", (exp), `"exp`", `__FILE__, `__LINE__)) begin \
    if (svunit_pkg::current_tc.is_running()) svunit_pkg::current_tc.give_up(); \
  end
`endif

`ifndef FAIL_IF_LOG
`define FAIL_IF_LOG(exp,msg) \
  if (svunit_pkg::current_tc.fail(`"fail_if`", (exp), `"exp`", `__FILE__, `__LINE__, msg)) begin \
    if (svunit_pkg::current_tc.is_running()) svunit_pkg::current_tc.give_up(); \
  end
`endif

`ifndef FAIL_IF_EQUAL
`define FAIL_IF_EQUAL(a,b) \
  if (svunit_pkg::current_tc.fail(`"fail_if_equal`", ((a)===(b)), `"(a) === (b)`", `__FILE__, `__LINE__)) begin \
    if (svunit_pkg::current_tc.is_running()) svunit_pkg::current_tc.give_up(); \
  end
`endif

`ifndef FAIL_UNLESS
`define FAIL_UNLESS(exp) \
  if (svunit_pkg::current_tc.fail(`"fail_unless`", !(exp), `"exp`", `__FILE__, `__LINE__)) begin \
    if (svunit_pkg::current_tc.is_running()) svunit_pkg::current_tc.give_up(); \
  end
`endif

`ifndef FAIL_UNLESS_LOG
`define FAIL_UNLESS_LOG(exp,msg) \
  if (svunit_pkg::current_tc.fail(`"fail_unless`", !(exp), `"exp`", `__FILE__, `__LINE__, msg)) begin \
    if (svunit_pkg::current_tc.is_running()) svunit_pkg::current_tc.give_up(); \
  end
`endif

`ifndef FAIL_UNLESS_EQUAL
`define FAIL_UNLESS_EQUAL(a,b) \
  if (svunit_pkg::current_tc.fail(`"fail_unless_equal`", ((a)!==(b)), `"(a) !== (b)`", `__FILE__, `__LINE__)) begin \
    if (svunit_pkg::current_tc.is_running()) svunit_pkg::current_tc.give_up(); \
  end
`endif

`ifndef FAIL_IF_STR_EQUAL
`define FAIL_IF_STR_EQUAL(a,b) \
  begin \
    string stra; \
    string strb; \
    stra = a; \
    strb = b; \
    if (svunit_pkg::current_tc.fail(`"fail_if_str_equal`", stra.compare(strb)==0, $sformatf(`"\"%s\" == \"%s\"`",stra,strb), `__FILE__, `__LINE__)) begin \
      if (svunit_pkg::current_tc.is_running()) svunit_pkg::current_tc.give_up(); \
    end \
  end
`endif

`ifndef FAIL_UNLESS_STR_EQUAL
`define FAIL_UNLESS_STR_EQUAL(a,b) \
  begin \
    string stra; \
    string strb; \
    stra = a; \
    strb = b; \
    if (svunit_pkg::current_tc.fail(`"fail_unless_str_equal`", stra.compare(strb)!=0, $sformatf(`"\"%s\" != \"%s\"`",stra,strb), `__FILE__, `__LINE__)) begin \
      if (svunit_pkg::current_tc.is_running()) svunit_pkg::current_tc.give_up(); \
    end \
  end
`endif


/*
  Macro: `INFO
  Displays info message to screen and in log file

  Parameters:
    msg - string to display
*/
`define INFO(msg) \
  $display("INFO:  [%0t][%0s]: %s", $time, name, msg)


/*
  Macro: `ERROR
  Displays error message to screen and in log file

  Parameters:
    msg - string to display
*/
`define ERROR(msg) \
  $display("ERROR: [%0t][%0s]: %s", $time, name, msg)


/*
  Macro: `LF
  Displays a blank line in log file
*/
`define LF $display("");


/*
  Macro: `SVUNIT_TESTS_BEGIN
  START a block of unit tests
*/
`define SVUNIT_TESTS_BEGIN \
  task automatic run(); \
    `INFO("RUNNING");

/*
  Macro: `SVUNIT_TESTS_END
  END a block of unit tests
*/
`define SVUNIT_TESTS_END endtask


/*
  Macro: `SVTEST
  START an svunit test within an SVUNIT_TEST_BEGIN/END block

  REQUIRES ACCESS TO error_count
*/
`define SVTEST(_NAME_) \
  begin : _NAME_ \
    string _testName = `"_NAME_`"; \
    integer local_error_count = svunit_ut.get_error_count(); \
    string fileName; \
    int lineNumber; \
\
    `INFO($sformatf(`"%s::RUNNING`", _testName)); \
    svunit_pkg::current_tc = svunit_ut; \
    svunit_ut.start(); \
    setup(); \
    fork \
      begin \
        fork \
          begin

/*
  Macro: `SVTEST_END
  END an svunit test within an SVUNIT_TEST_BEGIN/END block
*/
`define SVTEST_END \
          end \
          begin \
            if (svunit_ut.get_error_count() == local_error_count) begin \
              svunit_ut.wait_for_error(); \
            end \
          end \
          `SVUNIT_FUSE \
        join_any \
        #0; \
        disable fork; \
      end \
    join \
    svunit_ut.stop(); \
    teardown(); \
    if (svunit_ut.get_error_count() == local_error_count) \
      `INFO($sformatf(`"%s::PASSED`", _testName)); \
    else \
      `INFO($sformatf(`"%s::FAILED`", _testName)); \
    svunit_ut.update_exit_status(); \
  end

`define SVUNIT_FUSE \
`ifdef SVUNIT_TIMEOUT \
begin \
  bit svunit_timeout = 1; \
  #(`SVUNIT_TIMEOUT); \
  `FAIL_IF(svunit_timeout) \
end \
`endif

/*
  Macro: `SVUNIT_CLK_GEN(_clk_variable, _half_period)
  Generate a clock that runs only while this unit test
  is running.
*/
`define SVUNIT_CLK_GEN(_clk_variable, _half_period) \
    initial begin \
        _clk_variable = 0; \
        wait(svunit_ut != null); \
        forever begin \
            if( svunit_ut.is_running() ) \
                #_half_period _clk_variable = !_clk_variable; \
            else \
                wait( svunit_ut.is_running() ); \
        end \
    end   
