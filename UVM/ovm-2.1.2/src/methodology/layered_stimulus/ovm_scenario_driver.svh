// $Id: ovm_scenario_driver.svh,v 1.9 2008/08/07 15:18:05 jlrose Exp $
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


//typedef class ovm_scenario_controller_base;
//typedef class ovm_scenario_base;

virtual class ovm_scenario_driver #(type REQ = ovm_sequence_item, type RSP = REQ) 
  extends ovm_driver #(REQ, RSP);

typedef ovm_scenario_driver #(REQ, RSP) p_drv;
typedef ovm_sequencer #(REQ, RSP) sequencer_t;
ovm_seq_item_pull_port #(REQ, RSP) req_port;
ovm_seq_item_pull_port #(REQ, RSP) put_rsp;


function void set_scenario_controller(sequencer_t scenario_controller_ptr);
    seq_item_port.connect(scenario_controller_ptr.seq_item_export);
endfunction

function new (string name, ovm_component parent);
    super.new(name, parent);
    req_port = seq_item_port;
endfunction // new

function void end_of_elaboration();
    put_rsp = seq_item_port;
endfunction // void


///////////////////////////////////////////////////
//
// get_next_item
//   Called by the driver to issue a request from
//   the scenario_controller and return the next scenario item
///////////////////////////////////////////////////

  virtual task get_next_item(output REQ req_item, input bit non_blocking = 0);
    if (non_blocking == 0) begin
      seq_item_port.get(req_item);
      
    end
    else begin
      if (seq_item_port.has_do_available() == 0) begin
        req_item = null;
        return;
      end
      seq_item_port.get(req_item);
    end
  endtask  

  virtual task run();
  endtask // run

endclass

