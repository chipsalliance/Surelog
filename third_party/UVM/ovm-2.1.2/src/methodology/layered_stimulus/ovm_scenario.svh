//----------------------------------------------------------------------
//   Copyright 2007-2009 Mentor Graphics Corporation
//   Copyright 2007-2009 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------

virtual class ovm_scenario #(type REQ = ovm_sequence_item, type RSP = REQ) extends ovm_sequence #(REQ, RSP);

  ovm_scenario_controller_base m_scenario_controller;
  ovm_scenario_controller #(REQ, RSP) param_scenario_controller;



  function new(string name = "scenario");
    super.new(name);
  endfunction // new

  virtual function int get_id();
    return (get_sequence_id());
  endfunction

  virtual task start(ovm_scenario_controller_base sequencer,
                     ovm_scenario_base parent_sequence = null,
                     integer this_priority = 100,
                     bit call_pre_post = 1);
    
    m_scenario_controller = sequencer;
    $cast(param_scenario_controller, m_scenario_controller);
    call_pre_post = 1;
    super.start(sequencer, parent_sequence, this_priority, call_pre_post);
    if (sequencer != null) begin
      unlock();
    end
  endtask // start

virtual task pre_body();
    // Request a valid sequence_id();
    unlock();
    return;
endtask // pre_body

  virtual task apply_request(input REQ data_req, input bit randomize = 1);

    param_scenario_controller.apply_request(this, data_req, randomize);
  endtask
  
virtual task apply_send(input REQ data_req, input bit randomize = 1);
    param_scenario_controller.apply_send(this, data_req, randomize);
endtask    
    
virtual task apply(input REQ data_req, output RSP data_rsp, input bit randomize = 1);
  
    param_scenario_controller.apply(this, data_req, data_rsp, randomize);
endtask // apply

virtual task pre_apply();
    return;
endtask

virtual task mid_apply();
    return;
endtask

virtual task post_apply();
    return;
endtask // post_apply

  function string get_scenario_path_name();
    return (get_full_name());
  endfunction // string

endclass

