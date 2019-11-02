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
  Class: svunit_testsuite
  Base class for the unit test suite
*/
class svunit_testsuite extends svunit_base;

  /*
    Array: list_of_testcases
    Queue list of Unit Testcases to include for this Test Suite
  */
  local svunit_testcase list_of_testcases[$];


  /*
    Interface
  */
  extern function new(string name);
  extern function void add_testcase(svunit_testcase svunit);
  extern task run();

  extern function void report();

endclass


/*
  Constructor: new
  Initializes the test suite

  Parameters:
    name - instance name of the unit test suite
*/
function svunit_testsuite::new(string name);
  super.new(name);
endfunction


/*
  Method: add_testcase
  Adds a testcase to list of tests

  Parameters:
    svunit - unit test to add to the list of unit tests
*/
function void svunit_testsuite::add_testcase(svunit_testcase svunit);
  `INFO($sformatf("Registering Unit Test Case %s", svunit.get_name()));
  list_of_testcases.push_back(svunit); 
endfunction


/*
  Method: run
  Main Run Task of the Test Suite
*/
task svunit_testsuite::run();
  `INFO("RUNNING");
endtask


/*
  Method: report
  This task reports the results for the unit tests
*/
function void svunit_testsuite::report();
  int     pass_cnt;
  string  success_str;

  foreach(list_of_testcases[i])
    list_of_testcases[i].report();

  begin
    svunit_testcase match[$] = list_of_testcases.find() with (item.get_results() == PASS);
    pass_cnt = match.size();
  end
  
  if (pass_cnt == list_of_testcases.size()) begin
    success_str = "PASSED";
    success = PASS;
  end else begin
    success_str = "FAILED";
    success = FAIL;
  end

  `LF;
  `INFO($sformatf("%0s (%0d of %0d testcases passing)",
    success_str,
    pass_cnt,
    list_of_testcases.size()));
endfunction
