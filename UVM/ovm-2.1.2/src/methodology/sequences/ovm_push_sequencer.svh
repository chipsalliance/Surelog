//------------------------------------------------------------------------------
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
//------------------------------------------------------------------------------

typedef class ovm_sequence_base;

//------------------------------------------------------------------------------
//
// CLASS: ovm_push_sequencer #(REQ,RSP)
//
//------------------------------------------------------------------------------

class ovm_push_sequencer #(type REQ = ovm_sequence_item,
                           type RSP = REQ) extends ovm_sequencer_param_base #(REQ, RSP);

  typedef ovm_push_sequencer #( REQ , RSP) this_type;

  // Port: req_port
  //
  // The push sequencer requires access to a blocking put interface.
  // Continual sequence items, based on the list of available sequences
  // loaded into this sequencer, are sent out this port.

  ovm_blocking_put_port #(REQ) req_port;


  // Function: new
  //
  // Creates and initializes an instance of this class using the normal
  // constructor arguments for <ovm_component>: ~name~ is the name of the
  // instance, and ~parent~ is the handle to the hierarchical parent, if any.

  function new (string name, ovm_component parent);
    super.new(name, parent);
    req_port = new ("req_port", this);
  endfunction 


  // Task: run
  //
  // The push sequencer continuously selects from its list of available
  // sequences and sends the next item from the selected sequence out its
  // <req_port> using req_port.put(item). Typically, the req_port would be
  // connected to the req_export on an instance of an
  // <ovm_push_driver #(REQ,RSP)>, which would be responsible for
  // executing the item.

  task run();
    REQ t;
    int selected_sequence;

    fork
      super.run();
      forever
        begin
          do 
            begin
              wait_for_sequences();
              selected_sequence = choose_next_request();
              if (selected_sequence == -1) begin
                wait_for_available_sequence();
              end
            end while (selected_sequence == -1);
          // issue grant
          if (selected_sequence >= 0) begin
            set_arbitration_completed(arb_sequence_q[selected_sequence].request_id);
            arb_sequence_q.delete(selected_sequence);
            m_update_lists();
          end
          m_req_fifo.get(t);
          req_port.put(t);
          m_wait_for_item_sequence_id = t.get_sequence_id();
          m_wait_for_item_transaction_id = t.get_transaction_id();
        end // forever begin
    join
  endtask

  protected virtual function int  m_find_number_driver_connections();
    return(req_port.size());
  endfunction

endclass
