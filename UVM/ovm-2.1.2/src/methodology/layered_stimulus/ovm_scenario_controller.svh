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

typedef enum {FIFO, WEIGHTED, RANDOM, STRICT_FIFO, STRICT_RANDOM, USER} ARBITRATION_TYPE;

`ifndef INCA
// INCA doesn't like this 
typedef class ovm_scenario_base;
`endif

  
class ovm_scenario_controller #(type REQ = ovm_sequence_item, type RSP = REQ) extends ovm_sequencer #(REQ, RSP);

ovm_seq_item_pull_imp #(REQ, RSP, this_type) get_req_export;
ovm_sequence #(REQ, RSP) seq_ptr;

function new (string name, ovm_component parent);
    super.new(name, parent);
    count = 0;
    get_req_export = seq_item_export;
endfunction // new

///////////////////////////////////////////////////
//
// apply
//   send a scenario_item to the driver, and get
//   the response back
///////////////////////////////////////////////////

  virtual task apply_request(ovm_scenario_base scenario, input REQ data_req, input bit randomize = 1);
    wait_for_grant(scenario);
    scenario.pre_apply();
    if (randomize == 1) begin
      if (!data_req.randomize())
         ovm_report_warning ("RANDFL", "Randomization failed");
    end
    scenario.mid_apply();
  endtask
  
virtual task apply_send(ovm_scenario_base scenario, input REQ data_req, input bit randomize = 1);
    
    apply_request(scenario, data_req, randomize);
    send_request(scenario, data_req);
    scenario.post_apply();
endtask    
    
virtual task apply(ovm_scenario_base scenario, input REQ data_req, output RSP data_rsp, input bit randomize = 1);

    apply_send(scenario, data_req, randomize);
    
    if (!$cast(seq_ptr, scenario))
       ovm_report_fatal ("CASTFL", "Failed to cast scenario to a sequence", OVM_NONE);
    seq_ptr.get_response(data_rsp);
    scenario.post_apply();
endtask // apply

endclass

