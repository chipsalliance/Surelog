//----------------------------------------------------------------------
//   Copyright 2007-2011 Mentor Graphics Corporation
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


  typedef class ovm_sequence_base;

  /* deprecated */ typedef class ovm_seq_prod_if;
  /* deprecated */ typedef class ovm_seq_cons_if;

  typedef ovm_seq_item_pull_port #(ovm_sequence_item, ovm_sequence_item) ovm_seq_item_prod_if;


//------------------------------------------------------------------------------
//
// CLASS: ovm_sequencer #(REQ,RSP)
//
//------------------------------------------------------------------------------

class ovm_sequencer #(type REQ = ovm_sequence_item,
                      type RSP = REQ) extends ovm_sequencer_param_base #(REQ, RSP);

  typedef ovm_sequencer #( REQ , RSP) this_type;
  bit     sequence_item_requested = 0;
  bit     get_next_item_called    = 0;


  // Variable: seq_item_export
  //
  // This export provides access to this sequencer's implementation of the
  // sequencer interface, <sqr_if_base #(REQ,RSP)>, which defines the following
  // methods:
  //
  //|  virtual task          get_next_item      (output REQ request);
  //|  virtual task          try_next_item      (output REQ request);
  //|  virtual function void item_done          (input RSP response=null);
  //|  virtual task          wait_for_sequences ();
  //|  virtual function bit  has_do_available   ();
  //|  virtual task          get                (output REQ request);
  //|  virtual task          peek               (output REQ request);
  //|  virtual task          put                (input RSP response);
  //
  // See <sqr_if_base #(REQ,RSP)> for information about this interface.

  ovm_seq_item_pull_imp #(REQ, RSP, this_type) seq_item_export;


  // Deprecated Members, do not use
  /* deprecated */ ovm_seq_item_pull_imp #(REQ, RSP, this_type) seq_item_cons_if;
  /* deprecated */ ovm_seq_prod_if seq_prod_if;
  /* deprecated */ ovm_seq_cons_if seq_cons_if[string];


  // Function: new
  //
  // Creates and initializes an instance of this class using the normal
  // constructor arguments for ovm_component: name is the name of the instance,
  // and parent is the handle to the hierarchical parent, if any.

  function new (string name, ovm_component parent);
    super.new(name, parent);

    seq_item_export         = new ("seq_item_export", this);
    seq_item_cons_if             = seq_item_export;
    $cast(seq_prod_if, create_component("ovm_seq_prod_if", "seq_prod_if"));
    seq_prod_if.print_enabled = 0;
  endfunction // new
  
  // return proper type name string
  virtual function string get_type_name();
    return "ovm_sequencer";
  endfunction 

  function void connect();
    super.connect();
  endfunction // void

  virtual function void build();
    super.build();
  endfunction // function
  
  // Counting the number of of connections is done at end of
  // elaboration and the start of run.  If the user neglects to
  // call super in one or the other, the sequencer will still
  // have the correct value

  protected virtual function int  m_find_number_driver_connections();
    ovm_port_component_base provided_to_port_list[string];
    ovm_port_component_base seq_port_base;
    
    // Check that the seq_item_pull_port is connected
    seq_port_base = seq_item_export.get_comp();
    seq_port_base.get_provided_to(provided_to_port_list);
    return(provided_to_port_list.num());
  endfunction

  // Function: stop_sequences
  //
  // Tells the sequencer to kill all sequences and child sequences currently
  // operating on the sequencer, and remove all requests, locks and responses
  // that are currently queued.  This essentially resets the sequencer to an
  // idle state.

  virtual function void stop_sequences();
    REQ t;
    int reported  = 0;
    
    super.stop_sequences();
    sequence_item_requested  = 0;
    get_next_item_called     = 0;
    // Empty the request fifo
    while (m_req_fifo.try_get(t)) begin
      if (reported == 0) begin
        ovm_report_info(get_full_name(), "Sequences stopped.  Removing request from sequencer fifo");
        reported  = 1;
      end
//      void'(m_req_fifo.try_get(t));
    end
  endfunction // stop_sequences

  //============================================================================
  //
  // Internal Methods - do not use directly; they are subject to change or
  //                    elimination.
  //
  //============================================================================

  // Task- select_sequence

  local task select_sequence();
    int selected_sequence;

    // Select a sequence
    do begin
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
  endtask // select_sequence


  // Task- get_next_item
  //
  // private- access only via seq_item_export

  virtual task get_next_item(output REQ t);
    REQ     req_item;

    // If a sequence_item has already been requested, then get_next_item()
    // should not be called again until item_done() has been called.

    if (get_next_item_called == 1) begin
      ovm_report_error(get_full_name(), "Get_next_item called twice without item_done or get in between", OVM_NONE);
      return;
    end
    
    if (sequence_item_requested == 0) begin
      select_sequence();
    end

    // Set flag indicating that the item has been requested to ensure that item_done or get
    // is called between requests
    sequence_item_requested = 1;
    get_next_item_called = 1;
    m_req_fifo.peek(t);
  endtask // get_next_item


  // Task- try_next_item
  //
  // private- access only via seq_item_export

  virtual task try_next_item(output REQ t);
    int selected_sequence;
    time arb_time;
    ovm_sequence_base seq;

    if (get_next_item_called == 1) begin
      ovm_report_error(get_full_name(), "get_next_item/try_next_item called twice without item_done or get in between", OVM_NONE);
      return;
    end
    
    wait_for_sequences();
    selected_sequence = choose_next_request();
    if (selected_sequence == -1) begin
      t = null;
      return;
    end

    set_arbitration_completed(arb_sequence_q[selected_sequence].request_id);
    seq = arb_sequence_q[selected_sequence].sequence_ptr;
    arb_sequence_q.delete(selected_sequence);
    m_update_lists();
    sequence_item_requested = 1;
    get_next_item_called = 1;
    m_req_fifo.peek(t);
    
    wait_for_sequences();

    // attempt to get the item; if it fails, produce an error and return
    if (!m_req_fifo.try_peek(t))
      ovm_report_error("TRY_NEXT_BLOCKED", {"try_next_item: the selected sequence '",
        seq.get_full_name(), "' did not produce an item during wait_for_sequences(). ",
        "Sequences should not consume time between calls to start_item and finish_item. ",
        "Returning null item."}, OVM_NONE);

  endtask



  // Function- item_done
  //
  // private- access only via seq_item_export

  virtual function void item_done(RSP item = null);
    REQ t;

    // Set flag to allow next get_next_item or peek to get a new sequence_item
    sequence_item_requested = 0;
    get_next_item_called = 0;
    
    if (m_req_fifo.try_get(t) == 0) begin
      ovm_report_fatal(get_full_name(), "Item done reports empty request fifo", OVM_NONE);
    end else begin
      m_wait_for_item_sequence_id = t.get_sequence_id();
      m_wait_for_item_transaction_id = t.get_transaction_id();
    end
    
    if (item != null) begin
      seq_item_export.put_response(item);
    end

    // Grant any locks as soon as possible
    grant_queued_locks();
  endfunction // void


  // Task- put
  //
  // private- access only via seq_item_export

  virtual task put (RSP t);
    put_response(t);
  endtask // put


  // Task- get
  //
  // private- access only via seq_item_export

  task get(output REQ t);
    if (sequence_item_requested == 0) begin
      select_sequence();
    end
    sequence_item_requested = 1;
    m_req_fifo.peek(t);
    item_done();
  endtask // get


  // Task- peek
  //
  // private- access only via seq_item_export

  task peek(output REQ t);

    if (sequence_item_requested == 0) begin
      select_sequence();
    end
    
    // Set flag indicating that the item has been requested to ensure that item_done or get
    // is called between requests
    sequence_item_requested = 1;
    m_req_fifo.peek(t);
  endtask // peek


  // Function- item_done_trigger
  //
  // private - backwards compatibility

  function void item_done_trigger(RSP item = null);
    item_done(item);
  endfunction


  // Function- item_done_get_trigger_data
  //
  // private

  function RSP item_done_get_trigger_data();
    return last_rsp(0);
  endfunction


  // Function- add_seqs_cons_if
  //
  // private

  virtual function void add_seq_cons_if(string if_name);
    seq_cons_if[if_name] = null;
    $cast(seq_cons_if[if_name], create_component("ovm_seq_cons_if", 
      {"seq_cons_if[\"", if_name, "\"]"}));
    seq_cons_if[if_name].print_enabled = 0;
  endfunction  

endclass  

typedef ovm_sequencer #(ovm_sequence_item) ovm_virtual_sequencer;


//============================================================================
//
// Deprecated Classes - do not use
//
//============================================================================

class ovm_seq_prod_if extends ovm_component;

  string producer_name = "NOT CONNECTED";

  // constructor
  function new (string name="", ovm_component parent = null);
    super.new(name, parent);
  endfunction

  // data method do_print
  function void do_print (ovm_printer printer);
    super.do_print(printer);
    printer.print_string("sequence producer", producer_name);
  endfunction

  // polymorphic create method
  function ovm_object create (string name="");
    ovm_seq_prod_if i; i=new(name);
    return i;
  endfunction

  // return proper type name string
  virtual function string get_type_name();
    return "ovm_seq_prod_if";
  endfunction 

  // connect interface method for producer to consumer
  function void connect_if(ovm_seq_cons_if seq_if);
    ovm_component temp_comp;
    $cast(seq_if.consumer_seqr, get_parent());
    temp_comp = seq_if.get_parent();
    producer_name = temp_comp.get_full_name();
  endfunction

  // Macro to enable factory creation
  `ovm_component_registry(ovm_seq_prod_if, "ovm_seq_prod_if")

endclass

// Deprecated Class
class ovm_seq_cons_if extends ovm_component;

  // variable to hold the sequence consumer as an ovm_sequencer if the
  // consumer is that type
  ovm_sequencer #(ovm_sequence_item) consumer_seqr;

  // constructor
  function new (string name="", ovm_component parent = null);
    super.new(name, parent);
  endfunction

  // do_print for this object
  function void do_print (ovm_printer printer);
    super.do_print(printer);
    if (consumer_seqr != null)
      printer.print_string("sequence consumer", consumer_seqr.get_full_name());
    else
      printer.print_string("sequence consumer", "NOT_CONNECTED");
  endfunction

  // polymorphic creation
  function ovm_object create (string name="");
    ovm_seq_cons_if i; i=new(name);
    return i;
  endfunction

  // get_type_name implementation
  virtual function string get_type_name();
    return "ovm_seq_cons_if";
  endfunction 

  // method to connect this object to an ovm_sequence_prod_if
  function void connect_if(ovm_seq_prod_if seq_if);
    $cast(consumer_seqr, seq_if.get_parent());;
  endfunction

  // method to query who the current grabber of the connected sequencer is
  function ovm_sequence_base current_grabber();
    return consumer_seqr.current_grabber();
  endfunction
 
  // method to query if the connected sequencer is grabbed
  function bit is_grabbed();
    return consumer_seqr.is_grabbed();
  endfunction

  // method to start a sequence on the connected sequencer
  task start_sequence(ovm_sequence_base this_seq);
    consumer_seqr.start_sequence(this_seq);
  endtask

  // method to grab the connected sequencer
  virtual task grab(ovm_sequence_base this_seq);
    consumer_seqr.grab(this_seq);
  endtask

  // method to ungrab the connected sequencer
  virtual function void ungrab(ovm_sequence_base this_seq);
    consumer_seqr.ungrab(this_seq);
  endfunction

  // method to query if this interface object is connected
  function bit is_connected();
    if (consumer_seqr != null)
      return 1;
    else
      return 0;
  endfunction

  // method to query whether this interface is connected to a virtual sequencer
  // or sequencer
  function bit is_virtual_sequencer();
    ovm_virtual_sequencer vseqr;
    if (consumer_seqr == null)
      ovm_report_fatal("UNCSQR", "Cannot call connected_sequencer_type() on this unconnected interface.", OVM_NONE);
    else if (!$cast(vseqr, consumer_seqr))
      return 0;
    else
      return 1;
  endfunction

  // method to get the connecte sequencer's type name
  function string get_sequencer_type_name();
    if(consumer_seqr != null)
      return consumer_seqr.get_type_name();
    else
      return "NOT_CONNECTED";
  endfunction

  // Macro to enable factory creation
  `ovm_component_registry(ovm_seq_cons_if, "ovm_seq_cons_if")

endclass


