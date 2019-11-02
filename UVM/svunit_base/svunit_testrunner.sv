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
  Class: svunit_testrunner
  Base class for the test runner
*/
class svunit_testrunner extends svunit_base;

  /*
    Array: list_of_svunits
    Queue List of Test Suites to include in the Test Runner
  */
  local svunit_testsuite list_of_suites[$];


  /*
    Interface
  */
  extern function new(string name);
  extern function void add_testsuite(svunit_testsuite suite);

  extern function void report();

endclass


/*
  Constructor: name
  Initializes the test runner

  Parameters:
    name - instance name of the unit test runner
*/
function svunit_testrunner::new(string name);
  super.new(name);
endfunction


/*
  Method: add_testsuite
  Adds single testsuite to list of suites

  Parameters:
    suite - test suite to add to the list of test suites
*/
function void svunit_testrunner::add_testsuite(svunit_testsuite suite);
  `INFO($sformatf("Registering Test Suite %0s", suite.get_name()));
  list_of_suites.push_back(suite);
endfunction


/*
  Method: report
  This task reports the results for the test suites
*/
function void svunit_testrunner::report();
  int     pass_cnt;
  string  success_str;

  begin
    svunit_testsuite match[$] = list_of_suites.find() with (item.get_results() == PASS);
    pass_cnt = match.size();
  end

  if (pass_cnt == list_of_suites.size()) begin
    success_str = "PASSED";
    success = PASS;
  end else begin
    success_str = "FAILED";
    success = FAIL;
  end

  `LF;
  `INFO($sformatf("%0s (%0d of %0d suites passing) [%s]",
    success_str,
    pass_cnt,
    list_of_suites.size(),
    svunit_version));
endfunction
