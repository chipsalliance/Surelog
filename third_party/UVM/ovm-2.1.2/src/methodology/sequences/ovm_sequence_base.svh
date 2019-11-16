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


//------------------------------------------------------------------------------
//
// CLASS: ovm_sequence_base
//
// The ovm_sequence_base class provides the interfaces needed to create streams
// of sequence items and/or other sequences.
//
//------------------------------------------------------------------------------

class ovm_sequence_base extends ovm_sequence_item;

  protected ovm_sequence_state_enum   m_sequence_state;
            int                       m_next_transaction_id = 1;
  local     int                       m_priority = -1;
            int                       m_tr_handle;
            int                       m_wait_for_grant_semaphore;

  // Each sequencer will assign a sequence id.  When a sequence is talking to multiple
  // sequencers, each sequence_id is managed seperately
  protected int m_sqr_seq_ids[int];

  protected ovm_sequence_item response_queue[$];
  protected int               response_queue_depth = 8;
  protected bit               response_queue_error_report_disabled = 0;



  `ifndef INCA
  protected process  m_sequence_process;
  `else
  protected bit m_sequence_started = 0;
  protected event m_kill_event;
  `endif
  local bit                       m_use_response_handler = 0;

  // Variable: seq_kind
  //
  // Used as an identifier in constraints for a specific sequence type.

  rand int unsigned seq_kind;

  // For user random selection. This excludes the exhaustive and
  // random sequences.
  constraint pick_sequence { 
       (num_sequences() <= 2) || (seq_kind >= 2);
       (seq_kind <  num_sequences()) || (seq_kind == 0); }

  // bits to detect if is_relevant()/wait_for_relevant() are implemented
  local bit is_rel_default;
  local bit wait_rel_default;


  // Function: new
  //
  // The constructor for ovm_sequence_base. 
  //
  // The sequencer_ptr and parent_seq arguments are deprecated in favor of
  // their being set in the start method.  

  function new (string name = "ovm_sequence", 
                ovm_sequencer_base sequencer_ptr = null, 
                ovm_sequence_base parent_seq = null);
    static bit issued1=0,issued2=0;

    super.new(name);
    if (sequencer_ptr != null) begin
      if (!issued1) begin
        issued1=1;
        ovm_report_warning("deprecated",
          {"ovm_sequence::new()'s sequencer_ptr argument has been deprecated. ",
          "The sequencer is now specified at the time a sequence is started ",
          "using the start() task."});
      end
    end
    if (parent_seq != null) begin
      if (!issued2) begin
        issued2=1;
        ovm_report_warning("deprecated",
          {"ovm_sequence::new()'s parent_seq argument has been deprecated. ",
          "The parent sequence is now specified at the time a sequence is started ",
          "using the start() task."});
      end
    end
    m_sequence_state = CREATED;
    m_wait_for_grant_semaphore = 0;
  endfunction


  // Function: get_sequence_state
  //
  // Returns the sequence state as an enumerated value. Can use to wait on
  // the sequence reaching or changing from one or more states.
  //
  //| wait(get_sequence_state() & (STOPPED|FINISHED));

  function ovm_sequence_state_enum get_sequence_state();
    return m_sequence_state;
  endfunction


  // Task: wait_for_sequence_state
  // 
  // Waits until the sequence reaches the given ~state~. If the sequence
  // is already in this state, this method returns immediately. Convenience
  // for wait ( get_sequence_state == ~state~ );

  task wait_for_sequence_state(ovm_sequence_state_enum state);
    wait (m_sequence_state == state);
  endtask


  // Task: start
  //
  // The start task is called to begin execution of a sequence
  //
  // If parent_sequence is null, then the sequence is a parent, otherwise it is
  // a child of the specified parent.
  //
  // By default, the priority of a sequence is 100. A different priority may be
  // specified by this_priority. Higher numbers indicate higher priority.
  //
  // If call_pre_post is set to 1, then the pre_body and post_body tasks will
  // be called before and after the sequence body is called.

  virtual task start (ovm_sequencer_base sequencer,
                      ovm_sequence_base parent_sequence = null,
                      integer this_priority = 100,
                      bit call_pre_post = 1);

    if (parent_sequence != null) begin
      m_parent_sequence  = parent_sequence;
    end
    m_sequencer          = sequencer;
    m_priority           = this_priority;
  endtask

  function void stop();
    return;
  endfunction


  // Task: pre_body
  //
  // This task is a user-definable callback task that is called before the
  // execution of the body, unless the sequence is started with call_pre_post=0.
  // This method should not be called directly by the user.

  virtual task pre_body();  
    return;
  endtask


  // Task: post_body
  //
  // This task is a user-definable callback task that is called after the
  // execution of the body, unless the sequence is started with call_pre_post=0.
  // This method should not be called directly by the user.

  virtual task post_body();
    return;
  endtask
    

  // Task: pre_do
  //
  // This task is a user-definable callback task that is called after the
  // sequence has issued a wait_for_grant() call and after the sequencer has
  // selected this sequence, and before the item is randomized.  This method 
  // should not be called directly by the user.
  //
  // Although pre_do is a task, consuming simulation cycles may result in
  // unexpected behavior on the driver.

  virtual task pre_do(bit is_item);
    return;
  endtask


  // Task: body
  //
  // This is the user-defined task where the main sequence code resides.
  // This method should not be called directly by the user.

  virtual task body();
    ovm_report_warning("ovm_sequence_base", "Body definition undefined");
    return;
  endtask  


  // Function: is_item
  //
  // This function may be called on any sequence_item or sequence object.
  // It will return 1 on items and 0 on sequences.

  virtual function bit is_item();
    return(0);
  endfunction


  // Function: mid_do
  //
  // This function is a user-definable callback function that is called after
  // the sequence item has been randomized, and just before the item is sent
  // to the driver.  This mehod should not be called directly by the user.

  virtual function void mid_do(ovm_sequence_item this_item);
    return;
  endfunction
  
  
  // Function: post_do
  //
  // This function is a user-definable callback function that is called after
  // the driver has indicated that it has completed the item, using either
  // this item_done or put methods. This method should not be called directly
  // by the user.

  virtual function void post_do(ovm_sequence_item this_item);
    return;
  endfunction


  // Function: num_sequences
  // 
  // Returns the number of sequences in the sequencer's sequence library.

  function int num_sequences();
    if (m_sequencer == null) return (0);
    return (m_sequencer.num_sequences());
  endfunction


  // Function: get_seq_kind
  //
  // This function returns an int representing the sequence kind that has
  // been registerd with the sequencer.  The seq_kind int may be used with
  // the get_sequence or do_sequence_kind methods.

  function int get_seq_kind(string type_name);
    if(m_sequencer != null)
      return m_sequencer.get_seq_kind(type_name);
    else 
      ovm_report_warning("NULLSQ", $psprintf("%0s sequencer is null.",
                                           get_type_name()), OVM_NONE);
  endfunction


  // Function: get_sequence
  //
  // This function returns a reference to a sequence specified by req_kind,
  // which can be obtained using the get_seq_kind method.

  function ovm_sequence_base get_sequence(int unsigned req_kind);
    ovm_sequence_base m_seq;
    string m_seq_type;
    ovm_factory factory = ovm_factory::get();
    if (req_kind < 0 || req_kind >= m_sequencer.sequences.size()) begin
      ovm_report_error("SEQRNG", 
        $psprintf("Kind arg '%0d' out of range. Need 0-%0d",
        req_kind, m_sequencer.sequences.size()-1), OVM_NONE);
    end
    m_seq_type = m_sequencer.sequences[req_kind];
    if (!$cast(m_seq, factory.create_object_by_name(m_seq_type, get_full_name(), m_seq_type))) begin
      ovm_report_fatal("FCTSEQ", 
        $psprintf("Factory can not produce a sequence of type %0s.",
        m_seq_type), OVM_NONE);
    end
    m_seq.set_use_sequence_info(1);
    return m_seq;
  endfunction


  // Function: get_sequence_by_name
  //
  // Internal method.

  function ovm_sequence_base get_sequence_by_name(string seq_name);
    ovm_sequence_base m_seq;
    if (!$cast(m_seq, factory.create_object_by_name(seq_name, get_full_name(), seq_name))) begin
      ovm_report_fatal("FCTSEQ", 
        $psprintf("Factory can not produce a sequence of type %0s.", seq_name), OVM_NONE);
    end
    m_seq.set_use_sequence_info(1);
    return m_seq;
  endfunction


  // Task: do_sequence_kind
  //
  // This task will start a sequence of kind specified by req_kind, which can
  // be obtained using the get_seq_kind method.

  task do_sequence_kind(int unsigned req_kind);
    string m_seq_type;
    ovm_sequence_base m_seq;
    ovm_factory factory = ovm_factory::get();
    m_seq_type = m_sequencer.sequences[req_kind];
    if (!$cast(m_seq, factory.create_object_by_name(m_seq_type, get_full_name(), m_seq_type))) begin
      ovm_report_fatal("FCTSEQ", 
        $psprintf("Factory can not produce a sequence of type %0s.", m_seq_type), OVM_NONE);
    end
    m_seq.set_use_sequence_info(1);
    m_seq.set_parent_sequence(this);
    m_seq.set_sequencer(m_sequencer);
    m_seq.set_depth(get_depth() + 1);
    m_seq.reseed();
    
    start_item(m_seq);
    if(!m_seq.randomize()) begin
      ovm_report_warning("RNDFLD", "Randomization failed in do_sequence_kind()");
    end
    finish_item(m_seq);
  endtask


  // Task- create_and_start_sequence_by_name
  //
  // Internal method.

  task create_and_start_sequence_by_name(string seq_name);
    ovm_sequence_base m_seq;
    m_seq = get_sequence_by_name(seq_name);
    m_seq.start(m_sequencer, this, this.get_priority(), 0);
  endtask


  // Function: set_priority
  //
  // The priority of a sequence may be changed at any point in time.  When the
  // priority of a sequence is changed, the new priority will be used by the
  // sequencer the next time that it arbitrates between sequences.
  //
  // The default priority value for a sequence is 100.  Higher values result
  // in higher priorities.

  function void set_priority (int value);
    m_priority = value;
  endfunction


  // Function: get_priority
  //
  // This function returns the current priority of the sequence.

  function int get_priority();
    return (m_priority);
  endfunction


  // Task: wait_for_relevant
  //
  // This method is called by the sequencer when all available sequences are
  // not relevant.  When wait_for_relevant returns the sequencer attempt to
  // re-arbitrate. 
  //
  // Returning from this call does not guarantee a sequence is relevant,
  // although that would be the ideal. The method provide some delay to
  // prevent an infinite loop.
  //
  // If a sequence defines is_relevant so that it is not always relevant (by
  // default, a sequence is always relevant), then the sequence must also supply
  // a wait_for_relevant method.  

  virtual task wait_for_relevant();
    event e;
    wait_rel_default = 1;
    if (is_rel_default != wait_rel_default)
      ovm_report_fatal("RELMSM", 
        "is_relevant() was implemented without defining wait_for_relevant()", OVM_NONE);
    @e;  // this is intended to never return
  endtask
 

  // Function: is_relevant
  //
  // The default is_relevant implementation returns 1, indicating that the
  // sequence is always relevant.
  //
  // Users may choose to override with their own virtual function to indicate
  // to the sequencer that the sequence is not currently relevant after a
  // request has been made.
  //
  // When the sequencer arbitrates, it will call is_relevant on each requesting,
  // unblocked sequence to see if it is relevant. If a 0 is returned, then the
  // sequence will not be chosen.
  //
  // If all requesting sequences are not relevant, then the sequencer will call
  // wait_for_relevant on all sequences and re-arbitrate upon its return.
  //
  // Any sequence that implements is_relevant must also implement
  // wait_for_relevant so that the sequencer has a way to wait for a
  // sequence to become relevant.

  virtual function bit is_relevant(); 
    is_rel_default = 1;
    return 1;
  endfunction


  // Function: is_blocked
  //
  // Returns a bit indicating whether this sequence is currently prevented from
  // running due to another lock or grab. A 1 is returned if the sequence is
  // currently blocked. A 0 is returned if no lock or grab prevents this
  // sequence from executing. Note that even if a sequence is not blocked, it
  // is possible for another sequence to issue a lock or grab before this
  // sequence can issue a request.

  function bit is_blocked();
    return(m_sequencer.is_blocked(this));
  endfunction


  // Function: has_lock
  //
  // Returns 1 if this sequence has a lock, 0 otherwise.
  //
  // Note that even if this sequence has a lock, a child sequence may also have
  // a lock, in which case the sequence is still blocked from issuing
  // operations on the sequencer>

  function bit has_lock();
    return(m_sequencer.is_locked(this));
  endfunction


  // Task: lock
  //
  // Requests a lock on the specified sequencer. If sequencer is null, the lock
  // will be requested on the current default sequencer.
  //
  // A lock request will be arbitrated the same as any other request.  A lock is
  // granted after all earlier requests are completed and no other locks or
  // grabs are blocking this sequence.
  //
  // The lock call will return when the lock has been granted.

  task lock(ovm_sequencer_base sequencer = null);
    if (sequencer == null) begin
      if (m_sequencer == null) begin
        ovm_report_fatal("ISRELVNT", "Null m_sequencer reference", OVM_NONE);
      end
      m_sequencer.lock(this);
    end
    else begin
      sequencer.lock(this);
    end
  endtask


  // Task: grab
  // 
  // Requests a lock on the specified sequencer.  If no argument is supplied,
  // the lock will be requested on the current default sequencer.
  //
  // A grab equest is put in front of the arbitration queue. It will be
  // arbitrated before any other requests. A grab is granted when no other grabs
  // or locks are blocking this sequence.
  //
  // The grab call will return when the grab has been granted.

  task grab(ovm_sequencer_base sequencer = null);
    if (sequencer == null) begin
      if (m_sequencer == null) begin
        ovm_report_fatal("GRAB", "Null m_sequencer reference", OVM_NONE);
      end
      m_sequencer.grab(this);
    end
    else begin
      sequencer.grab(this);
    end
  endtask


  // Function: unlock
  //
  // Removes any locks or grabs obtained by this sequence on the specified
  // sequencer. If sequencer is null, then the unlock will be done on the
  // current default sequencer.

  function void  unlock(ovm_sequencer_base sequencer = null);
    if (sequencer == null) begin
      if (m_sequencer == null) begin
        ovm_report_fatal("UNLOCK", "Null m_sequencer reference", OVM_NONE);
      end
      m_sequencer.unlock(this);
    end else begin
      sequencer.unlock(this);
    end
  endfunction


  // Function: ungrab
  //
  // Removes any locks or grabs obtained by this sequence on the specified
  // sequencer. If sequencer is null, then the unlock will be done on the
  // current default sequencer.

  function void  ungrab(ovm_sequencer_base sequencer = null);
    unlock(sequencer);
  endfunction // void


  // Function: set_response_queue_error_report_disabled
  //
  // By default, if the response_queue overflows, an error is reported. The
  // response_queue will overflow if more responses are sent to this sequence
  // from the driver than get_response calls are made. Setting value to 0
  // disables these errors, while setting it to 1 enables them.

  function void set_response_queue_error_report_disabled(bit value);
    response_queue_error_report_disabled = value;
  endfunction

  
  // Function: get_response_queue_error_report_disabled
  //
  // When this bit is 0 (default value), error reports are generated when
  // the response queue overflows. When this bit is 1, no such error
  // reports are generated.

  function bit get_response_queue_error_report_disabled();
    return response_queue_error_report_disabled;
  endfunction


  // Function: set_response_queue_depth
  //
  // The default maximum depth of the response queue is 8. These method is used
  // to examine or change the maximum depth of the response queue.
  //
  // Setting the response_queue_depth to -1 indicates an arbitrarily deep
  // response queue.  No checking is done.

  function void set_response_queue_depth(int value);
    response_queue_depth = value;
  endfunction  


  // Function: get_response_queue_depth
  //
  // Returns the current depth setting for the response queue.

  function int get_response_queue_depth();
    return response_queue_depth;
  endfunction  


  // Function: clear_response_queue
  //
  // Empties the response queue for this sequence.

  virtual function void clear_response_queue();
    response_queue.delete();
  endfunction



  virtual function void put_base_response(input ovm_sequence_item response);
    if ((response_queue_depth == -1) ||
        (response_queue.size() < response_queue_depth)) begin
      response_queue.push_back(response);
      return;
    end
    if (response_queue_error_report_disabled == 0) begin
      ovm_report_error(get_full_name(), "Response queue overflow, response was dropped", OVM_NONE);
    end
  endfunction


  // Function- put_response
  //
  // Internal method.

  virtual function void put_response (ovm_sequence_item response_item);
    put_base_response(response_item);
  endfunction


  // Function- m_start_item
  //
  // Internal method.

  virtual task m_start_item(ovm_sequencer_base sequencer_ptr, ovm_sequence_item sequence_ptr,
                            int set_priority);
    ovm_sequence_base this_seq;
    
    if (this.get_sequencer() == null) begin
      if (!$cast(this_seq, sequence_ptr)) begin
        ovm_report_fatal("SEQMSTART", "Failure to cast sequence item", OVM_NONE);
      end
      set_use_sequence_info(1);
      set_parent_sequence(this_seq);
      set_sequencer(sequencer_ptr);
      reseed();
    end
    return;
  endtask  

  // Function- m_finish_item
  //
  // Internal method.

  virtual task m_finish_item(ovm_sequencer_base sequencer_ptr, 
                             ovm_sequence_item sequence_ptr, 
                             int set_priority = -1);
    ovm_sequence_base seq_base_ptr;

    if (!$cast(seq_base_ptr, sequence_ptr)) begin
        ovm_report_fatal("SEQMFINISH", "Failure to cast sequence item", OVM_NONE);
      end
    if (set_priority == -1) 
      begin
        if (get_priority() < 0) 
          begin
            start(sequencer_ptr, seq_base_ptr, 100, 0);
          end
        else 
          begin
            start(sequencer_ptr, seq_base_ptr, get_priority(), 0);
          end 
      end
    else 
      begin
        start(sequencer_ptr, seq_base_ptr, set_priority, 0);
      end
  endtask  


  // Task: wait_for_grant
  //
  // This task issues a request to the current sequencer.  If item_priority is
  // not specified, then the current sequence priority will be used by the
  // arbiter. If a lock_request is made, then the sequencer will issue a lock
  // immediately before granting the sequence.  (Note that the lock may be
  // granted without the sequence being granted if is_relevant is not asserted).
  //
  // When this method returns, the sequencer has granted the sequence, and the
  // sequence must call send_request without inserting any simulation delay
  // other than delta cycles.  The driver is currently waiting for the next
  // item to be sent via the send_request call.

  virtual task wait_for_grant(int item_priority = -1, bit lock_request = 0);
    if (m_sequencer == null) begin
      ovm_report_fatal("WAITGRANT", "Null m_sequencer reference", OVM_NONE);
    end
    m_sequencer.wait_for_grant(this, item_priority, lock_request);
  endtask


  // Function: send_request
  //
  // The send_request function may only be called after a wait_for_grant call. 
  // This call will send the request item to the sequencer, which will forward
  // it to the driver. If the rerandomize bit is set, the item will be
  // randomized before being sent to the driver.

  virtual function void send_request(ovm_sequence_item request, bit rerandomize = 0);
    if (m_sequencer == null) begin
        ovm_report_fatal("SENDREQ", "Null m_sequencer reference", OVM_NONE);
      end
    m_sequencer.send_request(this, request, rerandomize);
  endfunction


  // Task: wait_for_item_done
  //
  // A sequence may optionally call wait_for_item_done.  This task will block
  // until the driver calls item_done or put.  If no transaction_id parameter
  // is specified, then the call will return the next time that the driver calls
  // item_done or put.  If a specific transaction_id is specified, then the call
  // will return when the driver indicates completion of that specific item.
  //
  // Note that if a specific transaction_id has been specified, and the driver
  // has already issued an item_done or put for that transaction, then the call
  // will hang, having missed the earlier notification.


  virtual task wait_for_item_done(int transaction_id = -1);
    if (m_sequencer == null) begin
        ovm_report_fatal("WAITITEMDONE", "Null m_sequencer reference", OVM_NONE);
      end
    m_sequencer.wait_for_item_done(this, transaction_id);
  endtask


  // Function: set_sequencer
  //
  // Sets the default sequencer for the sequence to run on.  It will take
  // effect immediately, so it should not be called while the sequence is
  // actively communicating with the sequencer.

  virtual function void set_sequencer(ovm_sequencer_base sequencer);
    m_sequencer = sequencer;
  endfunction


  // Function: get_sequencer
  //
  // Returns a reference to the current default sequencer of the sequence.

  virtual function ovm_sequencer_base get_sequencer();
    return(m_sequencer);
  endfunction

  function void m_kill();
`ifndef INCA
    if (m_sequence_process != null) begin
      m_sequence_process.kill;
      m_sequence_process = null;
    end
`else
    ->m_kill_event;
    m_sequence_started=0;
`endif
    m_sequence_state = STOPPED;
  endfunction


  // Function: kill
  //
  // This function will kill the sequence, and cause all current locks and
  // requests in the sequence's default sequencer to be removed. The sequence
  // state will change to STOPPED, and its post_body() method, if  will not b
  //
  // If a sequence has issued locks, grabs, or requests on sequencers other than
  // the default sequencer, then care must be taken to unregister the sequence
  // with the other sequencer(s) using the sequencer unregister_sequence() 
  // method.

  function void kill();
`ifndef INCA
    if (m_sequence_process != null) begin
`else
    if (m_sequence_started != 0) begin
`endif
      // If we are not connected to a sequencer, then issue
      // kill locally.
      if (m_sequencer == null) begin
        m_kill();
        return;
      end
      // If we are attached to a sequencer, then the sequencer
      // will clear out queues, and then kill this sequence
      m_sequencer.kill_sequence(this);
      return;
    end
  endfunction


  // Function: use_response_handler
  //
  // When called with enable set to 1, responses will be sent to the response
  // handler. Otherwise, responses must be retrieved using get_response.
  //
  // By default, responses from the driver are retrieved in the sequence by
  // calling get_response.
  //
  // An alternative method is for the sequencer to call the response_handler
  // function with each response.

  function void use_response_handler(bit enable);
    m_use_response_handler = enable;
  endfunction


  // Function: get_use_response_handler
  //
  // Returns the state of the use_response_handler bit.

  function bit get_use_response_handler();
    return(m_use_response_handler);
  endfunction


  // Function: response_handler
  //
  // When the use_reponse_handler bit is set to 1, this virtual task is called
  // by the sequencer for each response that arrives for this sequence.

  virtual function void response_handler(ovm_sequence_item response);
    return;
  endfunction


  // Function- get_base_response

  virtual task get_base_response(output ovm_sequence_item response, input int transaction_id = -1);

    int queue_size, i;

    if (response_queue.size() == 0)
      wait (response_queue.size() != 0);

    if (transaction_id == -1) begin
      response = response_queue.pop_front();
      return;
    end

    forever begin
      queue_size = response_queue.size();
      for (i = 0; i < queue_size; i++) begin
        if (response_queue[i].get_transaction_id() == transaction_id) 
          begin
            $cast(response,response_queue[i]);
            response_queue.delete(i);
            return;
          end
      end
      wait (response_queue.size() != queue_size);
    end
  endtask


  // Function: create_item
  //
  // Create_item will create and initialize a sequence_item or sequence
  // using the factory.  The sequence_item or sequence will be initialized
  // to communicate with the specified sequencer.

  protected function ovm_sequence_item create_item(ovm_object_wrapper type_var, 
                                                   ovm_sequencer_base l_sequencer, string name);

  ovm_factory f_ = ovm_factory::get();
  $cast(create_item,  f_.create_object_by_type( type_var, this.get_full_name(), name ));

  create_item.set_use_sequence_info(1);
  create_item.set_parent_sequence(this);
  create_item.set_sequencer(l_sequencer);
  create_item.set_depth(get_depth() + 1);
  create_item.reseed();

  endfunction

  // Function: start_item
  //
  // start_item and finish_item together will initiate operation of either
  // a sequence_item or sequence object.  If the object has not been initiated 
  // using create_item, then start_item will be initialized in start_item
  // to use the default sequencer specified by m_sequencer.  Randomization
  // may be done between start_item and finish_item to ensure late generation
  //
  //| virtual task start_item(ovm_sequence_item item, int set_priority = -1);

  // Function: finish_item
  //
  // finish_item, together with start_item together will initiate operation of 
  // either a sequence_item or sequence object.  Finish_item must be called
  // after start_item with no delays or delta-cycles.  Randomization, or other
  // functions may be called between the start_item and finish_item calls.
  //
  //|virtual task finish_item(ovm_sequence_item item, int set_priority = -1);
  

  // Function- m_get_sqr_sequence_id
  //
  // Internal method.

  function int m_get_sqr_sequence_id(int sequencer_id, bit update_sequence_id);
    if (m_sqr_seq_ids.exists(sequencer_id)) begin
      if (update_sequence_id == 1) begin
        set_sequence_id(m_sqr_seq_ids[sequencer_id]);
      end
      return(m_sqr_seq_ids[sequencer_id]);
    end
    else begin
      if (update_sequence_id == 1) begin
        set_sequence_id(-1);
      end
      return(-1);
    end
  endfunction
  

  // Function- m_set_sqr_sequence_id
  //
  // Internal method.

  function void m_set_sqr_sequence_id(int sequencer_id, int sequence_id);
    m_sqr_seq_ids[sequencer_id] = sequence_id;
    set_sequence_id(sequence_id);
  endfunction


  //-----------------------------------------------------------------
  // Deprecated: OVM Layered stimulus backward compatibility
  //-----------------------------------------------------------------

  /* deprecated */ function int get_id();
    return (get_sequence_id());
  endfunction

  /* deprecated */ function ovm_sequence_base get_parent_scenario();
    return (m_parent_sequence);
  endfunction

  /* deprecated */ virtual task pre_apply();
    return;
  endtask

  /* deprecated */ virtual task mid_apply();
    return;
  endtask

  /* deprecated */ virtual task post_apply();
    return;
  endtask

endclass                

