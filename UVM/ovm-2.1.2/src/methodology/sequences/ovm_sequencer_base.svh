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

typedef class ovm_sequencer_base;

typedef enum {SEQ_TYPE_REQ, SEQ_TYPE_LOCK, SEQ_TYPE_GRAB} SEQ_REQ_TYPE;
typedef enum {SEQ_ARB_FIFO, SEQ_ARB_WEIGHTED, SEQ_ARB_RANDOM, SEQ_ARB_STRICT_FIFO, SEQ_ARB_STRICT_RANDOM, SEQ_ARB_USER} 
        SEQ_ARB_TYPE;

class seq_req_class;
  static int        g_request_id = 0;
  bit               grant;
  int               sequence_id;
  int               request_id;
  int               item_priority;
  SEQ_REQ_TYPE      request;
  ovm_sequence_base sequence_ptr;

  function new(string name= "");
  endfunction
endclass  


//------------------------------------------------------------------------------
//
// CLASS: ovm_sequencer_base
//
// Controls the flow of sequences, which generate the stimulus (sequence item
// transactions) that is passed on to drivers for execution.
//
//------------------------------------------------------------------------------

class ovm_sequencer_base extends ovm_component;

  protected seq_req_class       arb_sequence_q[$];

  // The arb_completed associative array is used to indicate when a particular request_id
  // has been completed.  The array in indexed by request_id, and sequences will wait based
  // on the request_id assigned in the arb_sequence_q
  protected bit                 arb_completed[int];

  protected ovm_sequence_base   lock_list[$];
  local     SEQ_ARB_TYPE        arbitration = SEQ_ARB_FIFO;
  protected ovm_sequence_base   reg_sequences[int];
  local     static int          g_sequence_id = 1;
  local     static int          g_sequencer_id = 1;
  protected int                 m_sequencer_id;
  protected int                 m_lock_arb_size;  // used for waiting processes
  protected int                 m_arb_size;       // used for waiting processes
  protected int                 m_wait_for_item_sequence_id, m_wait_for_item_transaction_id;

  // Variable: pound_zero_count
  //
  // Set this variable via set_config_int to set the number of delta cycles
  // to insert in the wait_for_sequences task. The delta cycles are used
  // to ensure that a sequence with back-to-back items has an opportunity
  // to fill the action queue when the driver uses the non-blocking try_get
  // interface.

            int unsigned        pound_zero_count = 6;

  protected int                 m_seq_item_port_connect_size;



  // Variable: count
  //
  // Sets the number of items to execute.
  //
  // Supercedes the max_random_count variable for ovm_random_sequence class
  // for backward compatibility.

  int count = -1;

  // testing fields
  int m_random_count = 0;
  int m_exhaustive_count = 0;
  int m_simple_count = 0;


  // Variable: max_random_count
  //
  // Set this variable via set_config_int to set the number of sequence items
  // to generate, at the discretion of the derived sequence. The predefined
  // ovm_random_sequence uses count to determine the number of random items
  // to generate.

  int unsigned max_random_count = 10;


  // Variable: max_random_depth
  //
  // Used for setting the maximum depth inside random sequences. 
  // (Beyond that depth, random creates only simple sequences.)

  int unsigned max_random_depth = 4;


  // Variable: default_sequence
  //
  // This property defines the sequence type (by name) that will be
  // auto-started. The default sequence is initially set to ovm_random_sequence.
  // It can be configured through the ovm_component's set_config_string method
  // using the field name "default_sequence".

  protected string default_sequence = "ovm_random_sequence";               


  // The sequeunce aray holds the type names of the sequence types registered
  // to this sequencer; the factory will actually create the instances on demand.

  string sequences[$];

  // The ids array associates each sequence entry (above) with an int
  // number. This allows sequences to be randomly selected by randomizing
  // a number between 0 and the sequences array size.

  protected int sequence_ids[string];

  // variable used to randomly select a sequence from the sequences array

  protected rand int seq_kind;

 
  // Function: new
  //
  // Creates and initializes an instance of this class using the normal
  // constructor arguments for ovm_component: name is the name of the
  // instance, and parent is the handle to the hierarchical parent.
  
  function new (string name, ovm_component parent);
    super.new(name, parent);
    m_sequencer_id = g_sequencer_id++;
    m_lock_arb_size = -1;
    m_seq_item_port_connect_size = -1;
    void'(get_config_string("default_sequence", default_sequence));
    void'(get_config_int("count", count));
    void'(get_config_int("max_random_count", max_random_count));
    void'(get_config_int("max_random_depth", max_random_depth));
    void'(get_config_int("pound_zero_count", pound_zero_count));
  endfunction // new



  virtual function void build();
    super.build();
    void'(get_config_string("default_sequence", default_sequence));
    void'(get_config_int("count", count));
    void'(get_config_int("max_random_count", max_random_count));
    void'(get_config_int("max_random_depth", max_random_depth));
    void'(get_config_int("pound_zero_count", pound_zero_count));
  endfunction // build


  // Task: start_default_sequence
  //
  // Sequencers provide the start_default_sequence task to execute the default
  // sequence in the run phase. This method is not intended to be called
  // externally, but may be overridden in a derivative sequencer class if 
  // special behavior is needed when the default sequence is started. The
  // user class <ovm_sequencer_param_base #(REQ,RSP)> implements this method.

  virtual task start_default_sequence();
  endtask


  // Function- do_print
  //
  // If overridden, call super.do_print()

  function void do_print (ovm_printer printer);
    super.do_print(printer);
    if(sequences.size() != 0) begin
      printer.print_string("default_sequence", default_sequence);
      printer.print_field("count", count, $bits(count), OVM_DEC);
      printer.print_field("max_random_count", max_random_count, 
        $bits(max_random_count), OVM_DEC);
      printer.print_array_header("sequences", sequences.size());
      for(int i=0; i<sequences.size(); ++i)
        printer.print_string($psprintf("[%0d]", i), sequences[i], "[");
      printer.print_array_footer();
      printer.print_field("max_random_depth", max_random_depth, 
        $bits(max_random_depth), OVM_DEC);
    end
  endfunction
 

  // Function- m_update_lists
  //
  // private

  protected function void m_update_lists();
    m_lock_arb_size++;
  endfunction // void


  // Function- display_queues
  //
  // private

  function string display_queues();
    string s;
    
    $sformat(s, "  -- arb i/id/type: ");
    foreach (arb_sequence_q[i]) begin
      $sformat(s, "%s %0d/%0d/%s ", s, i, arb_sequence_q[i].sequence_id, arb_sequence_q[i].request);
    end // UNMATCHED !!
    $sformat(s, "%s\n -- lock_list i/id: ", s);
    foreach (lock_list[i]) begin
      $sformat(s, "%s %0d/%0d",s, i, lock_list[i].get_sequence_id());
    end // UNMATCHED !!
    return(s);
  endfunction // string


  // Function- next_sequence_id
  //
  // private

  local function int next_sequence_id();
    return(g_sequence_id++);
  endfunction // int

  ///////////////////////////////////////////////////
  //
  // Local Sequence Registration Functions
  //
  ///////////////////////////////////////////////////

  protected virtual function int  m_find_number_driver_connections();
    return(0);
  endfunction


  // Function- register_sequence
  //
  // private

  virtual function int register_sequence(ovm_sequence_base sequence_ptr);

    if (sequence_ptr.m_get_sqr_sequence_id(m_sequencer_id, 1) > 0) begin
      return (sequence_ptr.get_sequence_id());
    end
    
    sequence_ptr.m_set_sqr_sequence_id(m_sequencer_id, next_sequence_id());
    reg_sequences[sequence_ptr.get_sequence_id()] = sequence_ptr;
    return(sequence_ptr.get_sequence_id());
  endfunction


  // Function- find_sequence
  //
  // private

  protected function ovm_sequence_base find_sequence(int sequence_id);
    ovm_sequence_base seq_ptr;
    int           i;
    
    // When sequence_id is -1, return the first available sequence.  This is used
    // when deleting all sequences
    if (sequence_id == -1) begin
      if (reg_sequences.first(i)) begin
        return(reg_sequences[i]);
      end
      return(null);
    end
    
    if (reg_sequences.exists(sequence_id) == 0) begin
//      ovm_report_warning("find_sequence", 
//                         $psprintf("Sequence %d doesn't exist (find_sequence)", sequence_id));
      return (null);
    end
    return(reg_sequences[sequence_id]);
  endfunction  


  // Function- unregister_sequence
  //
  // private

  protected virtual function void unregister_sequence(int sequence_id);
    if (reg_sequences.exists(sequence_id) == 0) begin
//      ovm_report_warning("unregister_sequence", 
//                         $psprintf("Sequence %d doesn't exist (unregister_sequence)", sequence_id));
      return;
    end
    reg_sequences.delete(sequence_id);
  endfunction  



  // Function: user_priority_arbitration
  //
  // If the sequencer arbitration mode is set to SEQ_ARB_USER (via the
  // ~set_arbitration~ method), then the sequencer will call this function each
  // time that it needs to arbitrate among sequences. 
  //
  // Derived sequencers may override this method to perform a custom arbitration
  // policy. Such an override must return one of the entries from the
  // avail_sequences queue, which are int indexes into an internal queue,
  // arb_sequence_q.
  //
  // The default implementation behaves like SEQ_ARB_FIFO, which returns the
  // entry at avail_sequences[0]. 
  //
  //-----
  // If a user specifies that the sequencer is to use user_priority_arbitration
  // through the call set_arbitration(SEQ_ARB_USER), then the sequencer will
  // call this function each time that it needs to arbitrate among sequences.
  //
  // This function must return an int that matches one of the available
  // sequences that is passed into the call through the avail_sequences parameter
  //
  // Each int in avail_sequences points to an entry in the arb_sequence_q, 
  // which is a protected queue that may be accessed from this function.
  //
  // To modify the operation of user_priority_arbitration, the function may
  // arbitrarily choose any sequence among the list of avail_sequences.  It is
  // important to choose only an available sequence.
  
  virtual function integer user_priority_arbitration(integer avail_sequences[$]);
    return (avail_sequences[0]);
  endfunction // user_priority_arbitration


  // Function- grant_queued_locks
  //
  // private
  //
  // Any lock or grab requests that are at the front of the queue will be
  // granted at the earliest possible time.  This function grants any queues
  // at the front that are not locked out

  protected function void grant_queued_locks();
    int i, temp;

    for (i = 0; i < arb_sequence_q.size(); i++) begin
      
      // Check for lock requests.  Any lock request at the head
      // of the queue that is not blocked will be granted immediately.
      temp = 0;
      if (i < arb_sequence_q.size()) begin
        if (arb_sequence_q[i].request == SEQ_TYPE_LOCK) begin
          temp = (is_blocked(arb_sequence_q[i].sequence_ptr) == 0);
        end
      end

      // Grant the lock request and remove it from the queue.
      // This is a loop to handle multiple back-to-back locks.
      // Since each entry is deleted, i remains constant
      while (temp) begin
        lock_list.push_back(arb_sequence_q[i].sequence_ptr);
        set_arbitration_completed(arb_sequence_q[i].request_id);
        arb_sequence_q.delete(i);
        m_update_lists();

        temp = 0;
        if (i < arb_sequence_q.size()) begin
          if (arb_sequence_q[i].request == SEQ_TYPE_LOCK) begin
            temp = is_blocked(arb_sequence_q[i].sequence_ptr) == 0;
          end
        end
      end
    end // for (i = 0; i < arb_sequence_q.size(); i++)
  endfunction // void

    
        
  // Function- choose_next_request
  //
  // private
  //
  // When a driver requests an operation, this function must find the next
  // available, unlocked, relevant sequence.
  //
  // This function returns -1 if no sequences are available or the entry into
  // arb_sequence_q for the chosen sequence

  protected function int choose_next_request();
    int i, temp;
    int avail_sequence_count;
    int sum_priority_val;
    integer avail_sequences[$];
    integer highest_sequences[$];
    int highest_pri;
    string  s;

    avail_sequence_count = 0;

    grant_queued_locks();

    for (i = 0; i < arb_sequence_q.size(); i++) begin
      // Search for available sequences.  If in SEQ_ARB_FIFO arbitration,
      // then just return the first available sequence.  Otherwise,
      // create a list for arbitration purposes.
      if (i < arb_sequence_q.size())
        if (arb_sequence_q[i].request == SEQ_TYPE_REQ)
          if (is_blocked(arb_sequence_q[i].sequence_ptr) == 0)
            if (arb_sequence_q[i].sequence_ptr.is_relevant() == 1) begin
              if (arbitration == SEQ_ARB_FIFO) begin
                return (i);
              end
              else avail_sequences.push_back(i);
            end
    end // for (i = 0; i < arb_sequence_q.size(); i++)

    // Return immediately if there are 0 or 1 available sequences
    if (arbitration == SEQ_ARB_FIFO) begin
      return (-1);
    end
    if (avail_sequences.size() < 1)  begin
      return (-1);
    end
    
    if (avail_sequences.size() == 1) begin
      return (avail_sequences[0]);
    end
    
    // If any locks are in place, then the available queue must
    // be checked to see if a lock prevents any sequence from proceeding
    if (lock_list.size() > 0) begin
      for (i = 0; i < avail_sequences.size(); i++) begin
        if (is_blocked(arb_sequence_q[avail_sequences[i]].sequence_ptr) != 0) begin
          avail_sequences.delete(i);
          i--;
        end
      end
      if (avail_sequences.size() < 1) return (-1);
      if (avail_sequences.size() == 1) return (avail_sequences[0]);
    end

    ///////////////////////////////////
    //  Weighted Priority Distribution
    ///////////////////////////////////
    if (arbitration == SEQ_ARB_WEIGHTED) begin
      sum_priority_val = 0;
      for (i = 0; i < avail_sequences.size(); i++) begin
        sum_priority_val += get_seq_item_priority(arb_sequence_q[avail_sequences[i]]);
      end
      
      // Pick an available sequence based on weighted priorities of available sequences
      temp = $urandom_range(sum_priority_val-1, 0);

      sum_priority_val = 0;
      for (i = 0; i < avail_sequences.size(); i++) begin
        if ((get_seq_item_priority(arb_sequence_q[avail_sequences[i]]) + 
             sum_priority_val) > temp) begin
          return (avail_sequences[i]);
        end
        sum_priority_val += get_seq_item_priority(arb_sequence_q[avail_sequences[i]]);
      end
      ovm_report_fatal("Sequencer", "OVM Internal error in weighted arbitration code", OVM_NONE);
    end // if (arbitration == SEQ_ARB_WEIGHTED)
    
    ///////////////////////////////////
    //  Random Distribution
    ///////////////////////////////////
    if (arbitration == SEQ_ARB_RANDOM) begin
      i = $urandom_range(avail_sequences.size()-1, 0);
      return (avail_sequences[i]);
    end

    ///////////////////////////////////
    //  Strict Fifo
    ///////////////////////////////////
    if ((arbitration == SEQ_ARB_STRICT_FIFO) || arbitration == SEQ_ARB_STRICT_RANDOM) begin
      highest_pri = 0;
      // Build a list of sequences at the highest priority
      for (i = 0; i < avail_sequences.size(); i++) begin
        if (get_seq_item_priority(arb_sequence_q[avail_sequences[i]]) > highest_pri) begin
          // New highest priority, so start new list
          `ovm_clear_queue(highest_sequences)
          highest_sequences.push_back(avail_sequences[i]);
          highest_pri = get_seq_item_priority(arb_sequence_q[avail_sequences[i]]);
        end
        else if (get_seq_item_priority(arb_sequence_q[avail_sequences[i]]) == highest_pri) begin
          highest_sequences.push_back(avail_sequences[i]);
        end
      end

      // Now choose one based on arbitration type
      if (arbitration == SEQ_ARB_STRICT_FIFO) begin
        return(highest_sequences[0]);
      end
      
      i = $urandom_range(highest_sequences.size()-1, 0);
      return (highest_sequences[i]);
    end // if ((arbitration == SEQ_ARB_STRICT_FIFO) || arbitration == SEQ_ARB_STRICT_RANDOM)

    if (arbitration == SEQ_ARB_USER) begin
      i = user_priority_arbitration( avail_sequences);

      // Check that the returned sequence is in the list of available sequences.  Failure to
      // use an available sequence will cause highly unpredictable results.
      highest_sequences = avail_sequences.find with (item == i);
      if (highest_sequences.size() == 0) begin
        ovm_report_fatal("Sequencer", $psprintf("Error in User arbitration, sequence %0d not available\n%s",
                                                i, display_queues()), OVM_NONE);
      end
      return(i);
    end
      
    ovm_report_fatal("Sequencer", "Internal error: Failed to choose sequence", OVM_NONE);

  endfunction // int

  protected task m_wait_arb_not_equal();
    wait (m_arb_size != m_lock_arb_size);
  endtask // m_wait_arb_not_equal


  // Task- wait_for_available_sequence
  //
  // private

  int m_is_relevant_completed;
  protected task wait_for_available_sequence();
    int i;
    int is_relevant_entries[$];

    // This routine will wait for a change in the request list, or for
    // wait_for_relevant to return on any non-relevant, non-blocked sequence
    m_arb_size = m_lock_arb_size;

    for (i = 0; i < arb_sequence_q.size(); i++) begin
      if (arb_sequence_q[i].request == SEQ_TYPE_REQ) begin
        if (is_blocked(arb_sequence_q[i].sequence_ptr) == 0) begin
          if (arb_sequence_q[i].sequence_ptr.is_relevant() == 0) begin
            is_relevant_entries.push_back(i);
          end
        end
      end
    end

    // Typical path - don't need fork if all queued entries are relevant
    if (is_relevant_entries.size() == 0) begin
      m_wait_arb_not_equal();
      return;
    end

    fork  // isolate inner fork block for disabling
      begin
        fork
          begin
            fork
	      begin
		// One path in fork is for any wait_for_relevant to return
		m_is_relevant_completed = 0;
		
		for(i = 0; i < is_relevant_entries.size(); i++) begin
                  fork
		    automatic int k = i;
		    
                    begin
                      arb_sequence_q[is_relevant_entries[k]].sequence_ptr.wait_for_relevant();
		      m_is_relevant_completed = 1;
                    end
                  join_none
		  
		end // for (i = 0; i < is_relevant_entries.size(); i++)
		wait (m_is_relevant_completed > 0);
	      end // fork begin
	      
              // The other path in the fork is for any queue entry to change
              begin
                m_wait_arb_not_equal();
              end
            join_any
          end
        join_any
        disable fork;
      end // fork
    join
  endtask // wait_for_available_sequence


  // Function- get_seq_item_priority
  //
  // private

  protected function int get_seq_item_priority(seq_req_class seq_q_entry);
    // If the priority was set on the item, then that is used
    if (seq_q_entry.item_priority != -1) begin
      if (seq_q_entry.item_priority <= 0) begin
        ovm_report_fatal("SEQITEMPRI", $psprintf("Sequence item from %s has illegal priority: %0d",
                                                 seq_q_entry.sequence_ptr.get_full_name(),
                                                 seq_q_entry.item_priority), OVM_NONE);
      end
      return (seq_q_entry.item_priority);
    end
    // Otherwise, use the priority of the calling sequence
    if (seq_q_entry.sequence_ptr.get_priority() < 0) begin
      ovm_report_fatal("SEQDEFPRI", $psprintf("Sequence %s has illegal priority: %0d",
                                               seq_q_entry.sequence_ptr.get_full_name(),
                                               seq_q_entry.sequence_ptr.get_priority()), OVM_NONE);
    end
    return (seq_q_entry.sequence_ptr.get_priority());
  endfunction
  

  // Task- wait_for_arbitration_completed
  //
  // private
  //
  // Waits until the current arbitration cycle is completed.

  task wait_for_arbitration_completed(int request_id);
    int lock_arb_size;
    
    // Search the list of arb_wait_q, see if this item is done
    forever 
      begin
        lock_arb_size  = m_lock_arb_size;
        
        if (arb_completed.exists(request_id)) begin
          arb_completed.delete(request_id);
          return;
        end
        wait (lock_arb_size != m_lock_arb_size);
      end
  endtask // wait_for_arbitration_completed


  // Function- set_arbitration_completed
  //
  // private

  function void set_arbitration_completed(int request_id);
    arb_completed[request_id] = 1;
  endfunction // void


  // Function: is_child
  //
  // Returns 1 if the child sequence is a child of the parent sequence,
  // 0 otherwise.

  function bit is_child (ovm_sequence_base parent, ovm_sequence_base child);
    ovm_sequence_base sequence_ptr;

    if (child == null) begin
      ovm_report_fatal("ovm_sequencer", "is_child passed null child", OVM_NONE);
    end

    if (parent == null) begin
      ovm_report_fatal("ovm_sequencer", "is_child passed null parent", OVM_NONE);
    end

    sequence_ptr = child.get_parent_sequence();
    while (sequence_ptr != null) begin
      if (sequence_ptr.get_inst_id() == parent.get_inst_id()) begin
        return (1);
      end
      sequence_ptr = sequence_ptr.get_parent_sequence();
    end
    return (0);
  endfunction // bit


  // Task: wait_for_grant
  //
  // This task issues a request for the specified sequence.  If item_priority
  // is not specified, then the current sequence priority will be used by the
  // arbiter.  If a lock_request is made, then the  sequencer will issue a lock
  // immediately before granting the sequence.  (Note that the lock may be
  // granted without the sequence being granted if is_relevant is not asserted).
  //
  // When this method returns, the sequencer has granted the sequence, and the
  // sequence must call send_request without inserting any simulation delay
  // other than delta cycles.  The driver is currently waiting for the next
  // item to be sent via the send_request call.
  
  virtual task wait_for_grant(ovm_sequence_base sequence_ptr, int item_priority = -1, bit lock_request = 0);
    seq_req_class req_s;
    int my_seq_id;

    if (sequence_ptr == null) begin
      ovm_report_fatal("ovm_sequencer", "wait_for_grant passed null sequence_ptr", OVM_NONE);
    end

    // Determine the number of drivers connected to this sequencer
    if(m_seq_item_port_connect_size < 0) begin
      m_seq_item_port_connect_size = m_find_number_driver_connections();
    end

`ifndef CDNS_NO_SQR_CON_CHK
    // If there are no drivers, then it is not possible to wait for grant
    if(m_seq_item_port_connect_size == 0) begin
      ovm_report_fatal("SQRWFG", "Wait_for_grant called on sequencer with no driver connected", OVM_NONE);
    end
`endif
    
    my_seq_id = register_sequence(sequence_ptr);
    
    // If lock_request is asserted, then issue a lock.  Don't wait for the response, since
    // there is a request immediately following the lock request
    if (lock_request == 1) begin
      req_s = new();
      req_s.grant = 0;
      req_s.sequence_id = my_seq_id;
      req_s.request = SEQ_TYPE_LOCK;
      req_s.sequence_ptr = sequence_ptr;
      req_s.request_id = req_s.g_request_id++;
      arb_sequence_q.push_back(req_s);
    end // lock_request == 1
        
    // Push the request onto the queue
    req_s = new();
    req_s.grant = 0;
    req_s.request = SEQ_TYPE_REQ;
    req_s.sequence_id = my_seq_id;
    req_s.item_priority = item_priority;
    req_s.sequence_ptr = sequence_ptr;
    req_s.request_id = req_s.g_request_id++;
    arb_sequence_q.push_back(req_s);
    m_update_lists();

    // Wait until this entry is granted
    // Continue to point to the element, since location in queue will change
    wait_for_arbitration_completed(req_s.request_id);

    // The wait_for_grant_semaphore is used only to check that send_request
    // is only called after wait_for_grant.  This is not a complete check, since
    // requests might be done in parallel, but it will catch basic errors
    req_s.sequence_ptr.m_wait_for_grant_semaphore++;

  endtask // wait_for_grant


  // task: wait_for_item_done
  //
  // A sequence may optionally call wait_for_item_done.  This task will block
  // until the driver calls item_done() or put() on a transaction issued by the
  // specified sequence.  If no transaction_id parameter is specified, then the
  // call will return the next time that the driver calls item_done() or put().
  // If a specific transaction_id is specified, then the call will only return
  // when the driver indicates that it has completed that specific item.
  //
  // Note that if a specific transaction_id has been specified, and the driver
  // has already issued an item_done or put for that transaction, then the call
  // will hang waiting for that specific transaction_id.

  virtual task wait_for_item_done(ovm_sequence_base sequence_ptr, int transaction_id);
    int sequence_id;

    sequence_id = sequence_ptr.m_get_sqr_sequence_id(m_sequencer_id, 1);
    m_wait_for_item_sequence_id = -1;
    m_wait_for_item_transaction_id = -1;

    if (transaction_id == -1) begin
      wait (m_wait_for_item_sequence_id == sequence_id);
    end else begin
      wait ((m_wait_for_item_sequence_id == sequence_id &&
             m_wait_for_item_transaction_id == transaction_id));
    end
  endtask // wait_for_item_done


  // Function: is_blocked
  //
  // Returns 1 if the sequence referred to by sequence_ptr is currently locked
  // out of the sequencer.  It will return 0 if the sequence is currently
  // allowed to issue operations.
  //
  // Note that even when a sequence is not blocked, it is possible for another
  // sequence to issue a lock before this sequence is able to issue a request
  // or lock.

  function bit is_blocked(ovm_sequence_base sequence_ptr);

    if (sequence_ptr == null)
      ovm_report_fatal("ovm_sequence_controller", "is_blocked passed null sequence_ptr", OVM_NONE);

      foreach (lock_list[i]) begin
        if ((lock_list[i].get_inst_id() != 
             sequence_ptr.get_inst_id()) &&
            (is_child(lock_list[i], sequence_ptr) == 0)) begin
          return (1);
        end
      end 
      return (0);
  endfunction //


  // Function: has_lock
  //
  // Returns 1 if the sequence refered to in the parameter currently has a lock
  // on this sequencer, 0 otherwise.
  //
  // Note that even if this sequence has a lock, a child sequence may also have
  // a lock, in which case the sequence is still blocked from issueing
  // operations on the sequencer

  function bit has_lock(ovm_sequence_base sequence_ptr);
    int my_seq_id;
    
    if (sequence_ptr == null)
      ovm_report_fatal("ovm_sequence_controller", "has_lock passed null sequence_ptr", OVM_NONE);
    my_seq_id = register_sequence(sequence_ptr);
      foreach (lock_list[i]) begin
        if (lock_list[i].get_inst_id() == sequence_ptr.get_inst_id()) begin
          return (1);
        end
      end 
    return (0);
  endfunction


  // Task- lock_req
  // 
  // Internal method. Called by a sequence to request a lock.
  // Puts the lock request onto the arbitration queue.
  
  local task lock_req(ovm_sequence_base sequence_ptr, bit lock);
    int my_seq_id;
    seq_req_class new_req;
    
    if (sequence_ptr == null)
      ovm_report_fatal("ovm_sequence_controller", "lock_req passed null sequence_ptr", OVM_NONE);

    my_seq_id = register_sequence(sequence_ptr);
    new_req = new();
    new_req.grant = 0;
    new_req.sequence_id = sequence_ptr.get_sequence_id();
    new_req.request = SEQ_TYPE_LOCK;
    new_req.sequence_ptr = sequence_ptr;
    new_req.request_id = new_req.g_request_id++;
    
    if (lock == 1) begin
      // Locks are arbitrated just like all other requests
      arb_sequence_q.push_back(new_req);
    end else begin
      // Grabs are not arbitrated - they go to the front
      // TODO:
      // Missing: grabs get arbitrated behind other grabs
      arb_sequence_q.push_front(new_req);
      m_update_lists();
    end

    // If this lock can be granted immediately, then do so.
    grant_queued_locks();
    
    wait_for_arbitration_completed(new_req.request_id);
  endtask
    

  // Task- unlock_req
  // 
  // Called by a sequence to request an unlock.  This
  // will remove a lock for this sequence if it exists
  
  function void unlock_req(ovm_sequence_base sequence_ptr);
    int my_seq_id;
    
    if (sequence_ptr == null) begin
      ovm_report_fatal("ovm_sequencer", "unlock_req passed null sequence_ptr", OVM_NONE);
    end
    my_seq_id = register_sequence(sequence_ptr);

    foreach (lock_list[i]) begin
      if (lock_list[i].get_inst_id() == sequence_ptr.get_inst_id()) begin
        lock_list.delete(i);
        m_update_lists();
        return;
      end
    end
    ovm_report_warning("SQRUNL", 
		       $psprintf("Sequence %s called ungrab / unlock, but didn't have lock",
				 sequence_ptr.get_full_name()),
		       OVM_NONE);
  endfunction // void


  // Task: lock
  //
  // Requests a lock for the sequence specified by sequence_ptr.
  //
  // A lock request will be arbitrated the same as any other request. A lock is
  // granted after all earlier requests are completed and no other locks or
  // grabs are blocking this sequence.
  //
  // The lock call will return when the lock has been granted.

  virtual task lock(ovm_sequence_base sequence_ptr);
    lock_req(sequence_ptr, 1);
  endtask // lock


  // Task: grab
  //
  // Requests a lock for the sequence specified by sequence_ptr. 
  //
  // A grab request is put in front of the arbitration queue. It will be
  // arbitrated before any other requests. A grab is granted when no other
  // grabs or locks are blocking this sequence.
  //
  // The grab call will return when the grab has been granted.

  virtual task grab(ovm_sequence_base sequence_ptr);
    lock_req(sequence_ptr, 0);
  endtask // lock


  // Function: unlock
  //
  // Removes any locks and grabs obtained by the specified sequence_ptr.

  virtual function void unlock(ovm_sequence_base sequence_ptr);
    unlock_req(sequence_ptr);
  endfunction // lock


  // Function: ungrab
  //
  // Removes any locks and grabs obtained by the specified sequence_ptr.

  virtual function void  ungrab(ovm_sequence_base sequence_ptr);
    unlock_req(sequence_ptr);
  endfunction // lock


  // Function- remove_sequence_from_queues

  local function void remove_sequence_from_queues(ovm_sequence_base sequence_ptr);
    int i;
    int seq_id;
    
    seq_id = sequence_ptr.m_get_sqr_sequence_id(m_sequencer_id, 0);
    
    // Remove all queued items for this sequence and any child sequences
    i = 0;
    do 
      begin
        if (arb_sequence_q.size() > i) begin
          if ((arb_sequence_q[i].sequence_id == seq_id) ||
              (is_child(sequence_ptr, arb_sequence_q[i].sequence_ptr))) begin
            if (sequence_ptr.get_sequence_state() == FINISHED)
              `ovm_error("SEQFINERR", $psprintf("Parent sequence '%s' should not finish before all items from itself and items from descendent sequences are processed.  The item request from the sequence '%s' is being removed.", sequence_ptr.get_full_name(), arb_sequence_q[i].sequence_ptr.get_full_name()))
            arb_sequence_q.delete(i);
            m_update_lists();
          end
          else begin
            i++;
          end
        end
      end
    while (i < arb_sequence_q.size());
    
    // remove locks for this sequence, and any child sequences
    i = 0;
    do
      begin
        if (lock_list.size() > i) begin
          if ((lock_list[i].get_inst_id() == sequence_ptr.get_inst_id()) ||
              (is_child(sequence_ptr, lock_list[i]))) begin
            if (sequence_ptr.get_sequence_state() == FINISHED)
              `ovm_error("SEQFINERR", $psprintf("Parent sequence '%s' should not finish before locks from itself and descedent sequences are removed.  The lock held by the child sequence '%s' is being removed.",sequence_ptr.get_full_name(), lock_list[i].get_full_name()))
            lock_list.delete(i);
            m_update_lists();
          end
          else begin
            i++;
          end
        end
      end
    while (i < lock_list.size());
    
    // Unregister the sequence_id, so that any returning data is dropped
    unregister_sequence(sequence_ptr.m_get_sqr_sequence_id(m_sequencer_id, 1));
  endfunction // void


  // Function: stop_sequences
  //
  // Tells the sequencer to kill all sequences and child sequences currently
  // operating on the sequencer, and remove all requests, locks and responses
  // that are currently queued.  This essentially resets the sequencer to an
  // idle state.

  virtual function void stop_sequences();
    ovm_sequence_base seq_ptr;
    
    seq_ptr = find_sequence(-1);
    while (seq_ptr != null)
      begin
        kill_sequence(seq_ptr);
        seq_ptr = find_sequence(-1);
      end
  endfunction // void
      

  // Function- sequence_exiting
  //
  // private
  
  function void sequence_exiting(ovm_sequence_base sequence_ptr);
    remove_sequence_from_queues(sequence_ptr);
  endfunction // void


  // Function- kill_sequence 
  //
  // private 

  function void kill_sequence(ovm_sequence_base sequence_ptr);
    int i;

    remove_sequence_from_queues(sequence_ptr);
    // kill the sequence
    sequence_ptr.m_kill();
  endfunction // void


  // Function: is_grabbed
  //
  // Returns 1 if any sequence currently has a lock or grab on this sequencer,
  // 0 otherwise.

  virtual function bit is_grabbed();
    return(lock_list.size() != 0);
  endfunction // bit


  // Function: current_grabber
  //
  // Returns a reference to the sequence that currently has a lock or grab on
  // the sequence.  If multiple hierarchical sequences have a lock, it returns
  // the child that is currently allowed to perform operations on the sequencer.

  virtual function ovm_sequence_base current_grabber();
    if (lock_list.size() == 0) begin
      return (null);
    end
    return (lock_list[lock_list.size()-1]);
  endfunction // ovm_sequence_base


  // Function: has_do_available
  //
  // Determines if a sequence is ready to supply a transaction.  A sequence
  // that obtains a transaction in pre-do must determine if the upstream object
  // is ready to provide an item
  //
  // Returns 1 if a sequence is ready to issue an operation. Returns 0 if no
  // unblocked, relevant sequence is requesting.

  virtual function bit has_do_available();
    
    foreach (arb_sequence_q[i]) begin
      if ((arb_sequence_q[i].sequence_ptr.is_relevant() == 1) &&
	  (is_blocked(arb_sequence_q[i].sequence_ptr) == 0)) begin
        return (1);
      end
    end
    return (0);
  endfunction


 
  // Function: set_arbitration
  //
  // Specifies the arbitration mode for the sequencer. It is one of
  //
  // SEQ_ARB_FIFO          - Requests are granted in FIFO order (default)
  // SEQ_ARB_WEIGHTED      - Requests are granted randomly by weight
  // SEQ_ARB_RANDOM        - Requests are granted randomly
  // SEQ_ARB_STRICT_FIFO   - Requests at highest priority granted in fifo order
  // SEQ_ARB_STRICT_RANDOM - Requests at highest priority granted in randomly
  // SEQ_ARB_USER          - Arbitration is delegated to the user-defined 
  //                         function, user_priority_arbitration. That function
  //                         will specify the next sequence to grant.
  //
  // The default user function specifies FIFO order.

  function void set_arbitration(SEQ_ARB_TYPE val);
    arbitration = val;
  endfunction

  function SEQ_ARB_TYPE get_arbitration();
    return (arbitration);
  endfunction // SEQ_ARB_TYPE


  // Function- analysis_write
  //
  // private

  virtual function void analysis_write(ovm_sequence_item t);
    return;
  endfunction


  //
  //
  // Methods available to Pull Drivers
  //
  //

  // Task: wait_for_sequences
  //
  // Waits for a sequence to have a new item available. The default
  // implementation in the sequencer delays pound_zero_count delta cycles.
  // (This variable is defined in ovm_sequencer_base.) User-derived sequencers
  // may override its wait_for_sequences implementation to perform some other
  // application-specific implementation.

  virtual task wait_for_sequences();
    for (int i = 0; i < pound_zero_count; i++) begin
      #0;
    end
  endtask // wait_for_sequences


  // Function: add_sequence
  //
  // Adds a sequence of type specified in the type_name paramter to the
  // sequencer's sequence library.

  function void add_sequence(string type_name);

    //assign typename key to an int based on size
    //used with get_seq_kind to return an int key to match a type name
    if (!sequence_ids.exists(type_name)) begin
      sequence_ids[type_name] = sequences.size();
      //used w/ get_sequence to return a ovm_sequence factory object that 
      //matches an int id
      sequences.push_back(type_name);
    end
  endfunction


  // Function- remove_sequence
  //
  // private

  function void remove_sequence(string type_name);
    sequence_ids.delete(type_name);
    for (int i = 0; i < sequences.size(); i++) begin
      if (sequences[i] == type_name)
        sequences.delete(i);
    end
  endfunction


  // Function- set_sequences_queue
  //
  // private

  function void set_sequences_queue(ref string sequencer_sequence_lib[$]);
    
    for(int j=0; j < sequencer_sequence_lib.size(); j++) begin
      sequence_ids[sequencer_sequence_lib[j]] = sequences.size();
      this.sequences.push_back(sequencer_sequence_lib[j]);
    end
  endfunction // void


  // Function: get_seq_kind
  //
  // Returns an int seq_kind correlating to the sequence of type type_name
  // in the sequencer�s sequence library. If the named sequence is not
  // registered a SEQNF warning is issued and -1 is returned.

  function int get_seq_kind(string type_name);

    if (sequence_ids.exists(type_name))
      return sequence_ids[type_name];

    ovm_report_warning("SEQNF", 
      $psprintf("Sequence type_name '%0s' not registered with this sequencer.",
      type_name), OVM_NONE);
    return -1;
  endfunction


  // Function: get_sequence
  //
  // Returns a reference to a sequence specified by the seq_kind int.
  // The seq_kind int may be obtained using the get_seq_kind() method.

function ovm_sequence_base get_sequence(int req_kind);

  ovm_factory factory = ovm_factory::get();
  ovm_sequence_base m_seq ;
  string m_seq_type;

  if (req_kind < 0 || req_kind >= sequences.size()) begin
    ovm_report_error("SEQRNG", 
      $psprintf("Kind arg '%0d' out of range. Need 0-%0d", 
      req_kind, sequences.size()-1));
  end

  m_seq_type = sequences[req_kind];
  if (!$cast(m_seq, factory.create_object_by_name(m_seq_type,
                                          get_full_name(),
                                          m_seq_type))) 
  begin
      ovm_report_fatal("FCTSEQ", 
        $psprintf("Factory can not produce a sequence of type %0s.",
        m_seq_type), OVM_NONE);
  end

  m_seq.print_sequence_info = 1;
  m_seq.set_sequencer (this);
  return m_seq;
  
endfunction // ovm_sequence_base


  // Function: num_sequences
  //
  // Returns the number of sequences in the sequencer�s sequence library.

  function int num_sequences();
    return (sequences.size());
  endfunction // num_sequences


  // Function: send_request
  //
  // Derived classes implement this function to send a request item to the
  // sequencer, which will forward it to the driver.  If the rerandomize bit
  // is set, the item will be randomized before being sent to the driver.
  //  
  // This function may only be called after a <wait_for_grant> call.

  virtual function void send_request(ovm_sequence_base sequence_ptr, ovm_sequence_item t, bit rerandomize = 0);
    return;
  endfunction


//
//
// Deprecated Methods
//
//

  // See has_lock.
  function bit is_locked(ovm_sequence_base sequence_ptr);
    return has_lock(sequence_ptr);
  endfunction



  virtual task start_sequence(ovm_sequence_base seq_base);
    static bit issued=0;
    if (!issued) begin
      issued=1;
      ovm_report_warning("deprecated",
        {"ovm_sequencer_base::start_sequence() has been deprecated and ",
        "replaced by the start() task, which becomes the only means ",
        "of starting sequences."}, OVM_NONE);
    end

    fork
      seq_base.start(this);
    join_none
  endtask // start_sequence

endclass


