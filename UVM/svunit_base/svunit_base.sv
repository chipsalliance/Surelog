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
  Class: svunit_base
  Base svunit class
*/
class svunit_base;

  /*
    String: name
    Name of class instance
  */
  protected string name;

  /*
    Variable: success
    Contains Pass or Fail for success of the Test
  */
  protected results_t success = PASS;

  /*
    Interface
  */
  extern function new(string name);
  extern function string get_name();
  extern function results_t get_results();

  extern virtual function void report();

endclass


/*
  Constructor: name
  Initializes the test

  Parameters:
    name - instance name of the unit test
*/
function svunit_base::new(string name);
  this.name = name;
endfunction


/*
  Function: get_name
  Returns instance name of the unit test
*/
function string svunit_base::get_name();
  return name;
endfunction


/*
  Method: report
  This task reports the result for the test
*/
function void svunit_base::report();
  string str = (success)? "PASSED":"FAILED";
  `INFO($sformatf("%0s::%0s", name, str));
endfunction


/*
  Function: get_results
  Returns success of the unit test case
*/
function results_t svunit_base::get_results();
  return success;
endfunction

