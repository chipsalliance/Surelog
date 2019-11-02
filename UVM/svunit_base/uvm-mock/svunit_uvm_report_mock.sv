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

class uvm_report_mock;
  static svunit_uvm_report_mock_expected_actual_container reports = new();

  static function void setup();
    reports.delete();
  endfunction

  static function int expected_cnt();
    return reports.expected.size();
  endfunction

  static function int actual_cnt();
    return reports.actual.size();
  endfunction

  `define EXPECT_SEVERITY(NAME, SEV) \
    static function void expect_``NAME(string id="", \
                                       string message=""); \
      reports.expected.push_back('{id, message, SEV}); \
    endfunction

  `EXPECT_SEVERITY(warning, UVM_WARNING)
  `EXPECT_SEVERITY(error,   UVM_ERROR)
  `EXPECT_SEVERITY(fatal,   UVM_FATAL)

  static function bit verify_complete();
    return reports.verify_complete();
  endfunction

  static function string dump();
    return reports.dump();
  endfunction
endclass
