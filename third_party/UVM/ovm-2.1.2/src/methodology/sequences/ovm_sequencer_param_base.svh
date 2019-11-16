//----------------------------------------------------------------------
//   Copyright 2007-2008 Mentor Graphics Corporation
//   Copyright 2007-2008 Cadence Design Systems, Inc.
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

class ovm_sequencer_param_base #(type REQ = ovm_sequence_item,
                                 type RSP = REQ) extends ovm_sequencer_base;

  typedef ovm_sequencer_param_base #( REQ , RSP) this_type;

//    static bit sequences[string] = '{default:0};

  REQ m_last_req_buffer[$];
  RSP m_last_rsp_buffer[$];

  protected int m_num_last_reqs = 1;
  protected int num_last_items = m_num_last_reqs;
  protected int m_num_last_rsps = 1;
  protected int m_num_reqs_sent = 0;
  protected int m_num_rsps_received = 0;

  // Response Analysis Fifo
  ovm_analysis_export #(RSP) rsp_export;
  sequencer_analysis_fifo #(RSP) sqr_rsp_analysis_fifo;

  // Fifo for handing reqests between scenario and driver
  tlm_fifo #(REQ) m_req_fifo;
  
  function new (string name, ovm_component parent);
    super.new(name, parent);

    rsp_export              = new("rsp_export", this);
    sqr_rsp_analysis_fifo   = new("sqr_rsp_analysis_fifo", this);
    sqr_rsp_analysis_fifo.print_enabled = 0;
    m_req_fifo              = new("req_fifo", this);
    m_req_fifo.print_enabled = 0;
  endfunction // new
  
  function void do_print (ovm_printer printer);
    super.do_print(printer);
    printer.print_field("num_last_reqs", m_num_last_reqs, $bits(m_num_last_reqs), OVM_DEC);
    printer.print_field("num_last_rsps", m_num_last_rsps, $bits(m_num_last_rsps), OVM_DEC);
  endfunction

  function void connect();
    rsp_export.connect(sqr_rsp_analysis_fifo.analysis_export);
  endfunction // void

  virtual function void build();
    super.build();
    sqr_rsp_analysis_fifo.sequencer_ptr = this;
  endfunction // function
  
  ///////////////////////////////////////////////////
  //
  // Local functions
  //
  ///////////////////////////////////////////////////

  
  ///////////////////////////////////////////////////
  //
  // Methods available to Sequencers
  // 
  ///////////////////////////////////////////////////
  
  virtual function void send_request(ovm_sequence_base sequence_ptr, ovm_sequence_item t, bit rerandomize = 0);
    REQ param_t;

    if (sequence_ptr == null) begin
      ovm_report_fatal("SNDREQ", "Send request sequence_ptr is null");
    end

    if (sequence_ptr.m_wait_for_grant_semaphore < 1) begin
      ovm_report_fatal("SNDREQ", "Send request called without wait_for_grant");
    end
    sequence_ptr.m_wait_for_grant_semaphore--;
    
    assert($cast(param_t, t)) begin
      if (param_t.get_transaction_id() == -1) begin
        param_t.set_transaction_id(sequence_ptr.m_next_transaction_id++);
      end
      m_last_req_push_front(param_t);
    end else begin
      ovm_report_fatal(get_name(),$psprintf("send_request failed to cast sequence item"));
//      $display("\nparam_t: %p\n\nt: %p\n\n", param_t, t);
    end

    param_t.set_sequence_id(sequence_ptr.m_get_sqr_sequence_id(m_sequencer_id, 1));
    t.set_sequencer(this);
    if (m_req_fifo.try_put(param_t) != 1) begin
      ovm_report_fatal(get_full_name(), 
                       $psprintf("Sequencer send_request not able to put to fifo, depth; %0d", m_req_fifo.size()));
    end

    m_num_reqs_sent++;
    // Grant any locks as soon as possible
    grant_queued_locks();
  endfunction
    
  function REQ get_current_item();
    REQ t;

    if (m_req_fifo.try_peek(t) == 0) begin
      return (null);
    end
    return(t);
  endfunction // REQ

  function void put_response (RSP t);
    ovm_sequence_base sequence_ptr;
    
    if (t == null) begin
      ovm_report_fatal("SQRPUT", "Driver put a null response");
    end
`ifndef CDNS_NO_SQR_CHK_SEQ_ID
    // Check that set_id_info was called
    if (t.get_sequence_id() == -1) begin
      ovm_report_fatal("SQRPUT", "Driver put a response with null sequence_id");
    end
`endif
      
    m_last_rsp_push_front(t);
    m_num_rsps_received++;

    sequence_ptr = find_sequence(t.get_sequence_id());

    if (sequence_ptr != null) begin
      // If the response_handler is enabled for this sequence, then call the response handler
      if (sequence_ptr.get_use_response_handler() == 1) begin
        sequence_ptr.response_handler(t);
        return;
      end
      
      sequence_ptr.put_response(t);
    end
    else begin
      ovm_report_info("Sequencer", $psprintf("Dropping response for sequence %0d, sequence not found", t.get_sequence_id()));
    end
  endfunction // void
  
  virtual function void analysis_write(ovm_sequence_item t);
    RSP response;

    assert($cast(response, t)) else begin
      ovm_report_fatal("ANALWRT", "Failure to cast analysis port write item");
    end
    put_response(response);
  endfunction
  
// start_default_sequence
// ----------------------

  task start_default_sequence();
    ovm_sequence_base m_seq ;

    if(sequences.size() != 0) begin
      
      //create the sequence object
      if (!$cast(m_seq, factory.create_object_by_name(default_sequence, 
                                                   get_full_name(), default_sequence))) 
        begin
          ovm_report_fatal("FCTSEQ", 
                           $psprintf("Default sequence set to invalid value : %0s.", 
                                     default_sequence));
        end

      assert(m_seq != null) else begin
        ovm_report_fatal("STRDEFSEQ", "Null m_sequencer reference");
      end
      m_seq.print_sequence_info = 1;
      m_seq.set_parent_sequence(null);
      m_seq.set_sequencer(this);
      m_seq.reseed();
      assert(m_seq.randomize()) else begin
        ovm_report_warning("STRDEFSEQ", "Failed to randomize sequence");
      end
      if(count != 0)
        m_seq.start(this);
    end
  endtask

  task run();
    start_default_sequence();
  endtask // run

  // get_num_reqs_sent
  // -----------------

  function int get_num_reqs_sent();
    return m_num_reqs_sent;
  endfunction

  // get_num_rsps_sent
  // -----------------

  function int get_num_rsps_received();
    return m_num_rsps_received;
  endfunction

  // set_num_last_reqs
  // -----------------

  function void set_num_last_reqs(int unsigned max);
    if(max > 1024) begin
      ovm_report_warning("HSTOB", 
        $psprintf("Invalid last size; 1024 is the maximum and will be used", max));
      max = 1024;
    end

    //shrink the buffer
    while((m_last_req_buffer.size() != 0) && (m_last_req_buffer.size() > max)) begin
      void'(m_last_req_buffer.pop_back());
    end

    m_num_last_reqs = max;
    num_last_items = max;

  endfunction

  // get_num_last_reqs
  // -----------------

  function int unsigned get_num_last_reqs();
    return m_num_last_reqs;
  endfunction

  // last_req
  // --------

  function REQ last_req(int unsigned n = 0);
    if(n > m_num_last_reqs) begin
      ovm_report_warning("HSTOB",
        $psprintf("Invalid last access (%0d), the max history is %0d", n,
        m_num_last_reqs));
      return null;
    end
    if(n == m_last_req_buffer.size())
      return null;
  
    return m_last_req_buffer[n];
  endfunction
  
  // m_last_req_push_front
  // --------------

  function void m_last_req_push_front(REQ item);
    if(!m_num_last_reqs)
      return;
 
    if(m_last_req_buffer.size() == m_num_last_reqs)
      void'(m_last_req_buffer.pop_back());

    this.m_last_req_buffer.push_front(item);
  endfunction

  // set_num_last_rsps
  // -----------------

  function void set_num_last_rsps(int unsigned max);
    if(max > 1024) begin
      ovm_report_warning("HSTOB", 
        $psprintf("Invalid last size; 1024 is the maximum and will be used", max));
      max = 1024;
    end

    //shrink the buffer
    while((m_last_rsp_buffer.size() != 0) && (m_last_rsp_buffer.size() > max)) begin
      void'(m_last_rsp_buffer.pop_back());
    end

    m_num_last_rsps = max;

  endfunction

  // get_num_last_rsps
  // -----------------

  function int unsigned get_num_last_rsps();
    return m_num_last_rsps;
  endfunction

  // last_rsp
  // --------

  function RSP last_rsp(int unsigned n = 0);
    if(n > m_num_last_rsps) begin
      ovm_report_warning("HSTOB",
        $psprintf("Invalid last access (%0d), the max history is %0d", n,
        m_num_last_rsps));
      return null;
    end
    if(n == m_last_rsp_buffer.size())
      return null;
  
    return m_last_rsp_buffer[n];
  endfunction
  
  // m_last_rsp_push_front
  // --------------

  function void m_last_rsp_push_front(RSP item);
    if(!m_num_last_rsps)
      return;
 
    if(m_last_rsp_buffer.size() == m_num_last_rsps)
      void'(m_last_rsp_buffer.pop_back());

    this.m_last_rsp_buffer.push_front(item);
  endfunction

virtual task execute_item(ovm_sequence_item item);
    ovm_sequence_base temp_seq;
    
    temp_seq = new();
    item.set_sequencer(this);
    item.set_parent_sequence(temp_seq);
    temp_seq.set_sequencer(this);
    temp_seq.start_item(item);
    temp_seq.finish_item(item);
endtask // execute_item

  virtual function void m_add_builtin_seqs(bit add_simple = 1);
    if(!sequence_ids.exists("ovm_random_sequence"))
      add_sequence("ovm_random_sequence");
    if(!sequence_ids.exists("ovm_exhaustive_sequence"))
      add_sequence("ovm_exhaustive_sequence");
    if(add_simple == 1)
      if(!sequence_ids.exists("ovm_simple_sequence"))
        add_sequence("ovm_simple_sequence");
  endfunction

  ///////////////////////////////////////////////////
  //
  // Backwards Compat
  // 
  ///////////////////////////////////////////////////

  // set_num_last_items
  // ----------------

  function void set_num_last_items(int unsigned max);
    set_num_last_reqs(max);
  endfunction

  // last
  // ----

  function ovm_sequence_item last(int unsigned n);
    return last_req(n);
  endfunction

endclass

  

