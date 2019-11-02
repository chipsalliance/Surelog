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


class svunit_uvm_report_mock_expected_actual_container extends uvm_report_catcher;
`ifdef UVM_VERSION_1_2
  typedef uvm_severity uvm_severity_type;
`endif

  typedef struct {
    string        id;
    string        msg;
    uvm_severity  sev;
  } catch_t;

  catch_t     expected[$];
  catch_t     actual[$];

  function new(string name="");
    super.new(name);
  endfunction

  function void delete();
    expected.delete();
    actual.delete();
  endfunction

  function action_e catch();
    uvm_severity_type sev_t = uvm_severity_type'(get_severity());

    if (sev_t == UVM_INFO) return THROW;

    actual.push_back('{get_id(), get_message(), get_severity()});
    // prevent the message from being displayed
    return CAUGHT;
  endfunction

  local function bit match_at_idx(int i);
    bit match = 0;
    if (expected[i].id  == "") match = 1;
    else                       match =  (expected[i].id  == actual[i].id);
    if (expected[i].msg == "") match &= 1;
    else                       match &= (expected[i].msg == actual[i].msg);
    match &= (expected[i].sev == actual[i].sev);
    return match;
  endfunction

  function bit verify_complete();
    if (expected.size() != actual.size()) begin
      $display("%s", dump());
      return 0;
    end

    foreach (expected[i]) begin
      if (!match_at_idx(i)) begin
        $display("%s", dump());
        return 0;
      end
    end

    return 1;
  endfunction

  function string dump();
    string id;
    string msg;
    uvm_severity_type sev;
    string s_sev;
    int i_max = (expected.size() > actual.size()) ? expected.size() : actual.size();

    dump = "uvm_report_mock::dump\n";
    for (int i=0; i<i_max; i+=1) begin
      if (i <= expected.size()-1) begin
        if (expected[i].id != "") $sformat(id, "\"%s\"", expected[i].id);
        else id = "\"*\"";
        id = truncate(id);
        if (expected[i].msg != "") $sformat(msg, "\"%s\"", expected[i].msg);
        else msg = "\"*\"";
        sev = uvm_severity_type'(expected[i].sev);
        $sformat(s_sev, "%s", sev.name());
      end
      else none_reported(id, msg, s_sev);

      $sformat(dump, "%s%0d:   EXPECTED => %14s %22s %s\n", dump, i, s_sev, id, msg);


      if (i <= actual.size()-1) begin
        $sformat(id, "\"%s\"", actual[i].id);;
        id = truncate(id);
        $sformat(msg, "\"%s\"", actual[i].msg);;
        sev = uvm_severity_type'(actual[i].sev);
        $sformat(s_sev, "%s", sev.name());
      end
      else none_reported(id, msg, s_sev);

      $sformat(dump, "%s     ACTUAL   => %14s %22s %s\n", dump, s_sev, id, msg);
    end
  endfunction

  local function void none_reported(ref string id,
                                   string msg,
                                   string s_sev);
    id = "";
    msg = "";
    s_sev = "None reported";
  endfunction

  local function string truncate(string s, int len = 22);
    if (s.len() > len) begin
      s = s.substr(0,len-1);
      s[s.len()-1] = "\"";
    end
    return s;
  endfunction
endclass
