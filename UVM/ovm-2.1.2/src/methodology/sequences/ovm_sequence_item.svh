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

`ifndef OVM_SEQUENCE_ITEM_SVH
`define OVM_SEQUENCE_ITEM_SVH

typedef class ovm_sequence_base;
typedef class ovm_sequencer_base;


//------------------------------------------------------------------------------
//
// CLASS: ovm_sequence_item
//
// The base class for user-defined sequence items and also the base class for
// the ovm_sequence class. The ovm_sequence_item class provides the basic
// functionality for objects, both sequence items and sequences, to operate in
// the sequence mechanism.
//
//------------------------------------------------------------------------------

class ovm_sequence_item extends ovm_transaction;

local      int                m_sequence_id = -1;
protected  bit                m_use_sequence_info = 0;
protected  int                m_depth = -1;
protected  ovm_sequencer_base m_sequencer = null;
protected  ovm_sequence_base  m_parent_sequence = null;
static     bit issued1=0,issued2=0;
bit        print_sequence_info = 0;


  // Function: new
  //
  // The constructor method for ovm_sequence_item. The sequencer and
  // parent_sequence may be specified in the constructor, or directly using
  // ovm_sequence_item methods.
  
  function new (string             name = "ovm_sequence_item",
                ovm_sequencer_base sequencer = null,
                ovm_sequence_base  parent_sequence = null);
    super.new(name);
    if (sequencer != null) begin
      if (!issued1) begin
        issued1=1;
        ovm_report_warning("deprecated",
                           {"ovm_sequence_item::new()'s sequencer_ptr argument has been deprecated. ",
                            "The sequencer is now specified at the time a sequence is started ",
                            "using the start() task."});
      end
      m_sequencer = sequencer;
    end
    if (parent_sequence != null) begin
      if (!issued2) begin
        issued2=1;
        ovm_report_warning("deprecated",
          {"ovm_sequence_item::new()'s parent_sequence argument has been deprecated. ",
           "The parent sequence is now specified at the time a sequence is started ",
           "using the start() task."});
      end
      m_parent_sequence = parent_sequence;
    end
  endfunction // new

  function string get_type_name();
    return "ovm_sequence_item";
  endfunction 

  // Macro for factory creation
  `ovm_object_registry(ovm_sequence_item, "ovm_sequence_item")


  // Function- set_sequence_id

  function void set_sequence_id(int id);
    m_sequence_id = id;
  endfunction


  // Function: get_sequence_id
  //
  // private
  //
  // Get_sequence_id is an internal method that is not intended for user code.
  // The sequence_id is not a simple integer.  The get_transaction_id is meant
  // for users to identify specific transactions.
  // 
  // These methods allow access to the sequence_item sequence and transaction
  // IDs. get_transaction_id and set_transaction_id are methods on the
  // ovm_transaction base_class. These IDs are used to identify sequences to
  // the sequencer, to route responses back to the sequence that issued a
  // request, and to uniquely identify transactions.
  //
  // The sequence_id is assigned automatically by a sequencer when a sequence
  // initiates communication through any sequencer calls (i.e. `ovm_do_xxx,
  // wait_for_grant).  A sequence_id will remain unique for this sequence
  // until it ends or it is killed.  However, a single sequence may have
  // multiple valid sequence ids at any point in time.  Should a sequence 
  // start again after it has ended, it will be given a new unique sequence_id.
  //
  // The transaction_id is assigned automatically by the sequence each time a
  // transaction is sent to the sequencer with the transaction_id in its
  // default (-1) value.  If the user sets the transaction_id to any non-default
  // value, that value will be maintained.
  //
  // Responses are routed back to this sequences based on sequence_id. The
  // sequence may use the transaction_id to correlate responses with their
  // requests.

  function int get_sequence_id();
    return (m_sequence_id);
  endfunction


  // Function: set_use_sequence_info
  //

  function void set_use_sequence_info(bit value);
    m_use_sequence_info = value;
  endfunction


  // Function: get_use_sequence_info
  //
  // These methods are used to set and get the status of the use_sequence_info
  // bit. Use_sequence_info controls whether the sequence information
  // (sequencer, parent_sequence, sequence_id, etc.) is printed, copied, or
  // recorded. When use_sequence_info is the default value of 0, then the
  // sequence information is not used. When use_sequence_info is set to 1,
  // the sequence information will be used in printing and copying.

  function bit get_use_sequence_info();
    return (m_use_sequence_info);
  endfunction


  // Function: set_id_info
  //
  // Copies the sequence_id and transaction_id from the referenced item into
  // the calling item.  This routine should always be used by drivers to
  // initialize responses for future compatibility.

  function void set_id_info(ovm_sequence_item item);
    if (item == null) begin
      ovm_report_fatal(get_full_name(), "set_id_info called with null parameter", OVM_NONE);
    end
    this.set_transaction_id(item.get_transaction_id());
    this.set_sequence_id(item.get_sequence_id());
  endfunction


  // Function: set_sequencer

  function void set_sequencer(ovm_sequencer_base sequencer);
    m_sequencer = sequencer;
    m_set_p_sequencer();
  endfunction // void


  // Function: get_sequencer
  //
  // These routines set and get the reference to the sequencer to which this
  // sequence_item communicates.

  function ovm_sequencer_base get_sequencer();
    return (m_sequencer);
  endfunction // ovm_sequencer_base


  // Function: set_parent_sequence
  //
  // Sets the parent sequence of this sequence_item.  This is used to identify
  // the source sequence of a sequence_item.

  function void set_parent_sequence(ovm_sequence_base parent);
    m_parent_sequence = parent;
  endfunction


  // Function: get_parent_sequence
  //
  // Returns a reference to the parent sequence of any sequence on which this
  // method was called. If this is a parent sequence, the method returns null.

  function ovm_sequence_base get_parent_sequence();
    return (m_parent_sequence);
  endfunction 


  // Function: set_depth
  //
  // The depth of any sequence is calculated automatically.  However, the user
  // may use  set_depth to specify the depth of a particular sequence. This
  // method will override the automatically calculated depth, even if it is
  // incorrect.  

  function void set_depth(int value);
    m_depth = value;
  endfunction


  // Function: get_depth
  //
  // Returns the depth of a sequence from it's parent.  A  parent sequence will
  // have a depth of 1, it's child will have a depth  of 2, and it's grandchild
  // will have a depth of 3.

  function int get_depth();

    // If depth has been set or calculated, then use that
    if (m_depth != -1) begin
      return (m_depth);
    end

    // Calculate the depth, store it, and return the value
    if (m_parent_sequence == null) begin
      m_depth = 1;
    end else begin
      m_depth = m_parent_sequence.get_depth() + 1;
    end

    return (m_depth);
  endfunction 


  // Function: is_item
  //
  // This function may be called on any sequence_item or sequence. It will
  // return 1 for items and 0 for sequences (which derive from this class).

  virtual function bit is_item();
    return(1);
  endfunction


  // Function: start_item
  //
  // start_item and finish_item together will initiate operation of either
  // a sequence_item or sequence object.  If the object has not been initiated 
  // using create_item, then start_item will be initialized in start_item
  // to use the default sequencer specified by m_sequencer.  Randomization
  // may be done between start_item and finish_item to ensure late generation

  virtual task start_item(ovm_sequence_item item, int set_priority = -1);
    if(item == null)
      m_sequencer.ovm_report_fatal("NULLITM", {"attempting to start a null item from item/sequence '", get_full_name(), "'"}, OVM_NONE);
    item.m_start_item(m_sequencer, this, set_priority);
  endtask  


  // Function: finish_item
  //
  // finish_item, together with start_item together will initiate operation of 
  // either a sequence_item or sequence object.  Finish_item must be called
  // after start_item with no delays or delta-cycles.  Randomization, or other
  // functions may be called between the start_item and finish_item calls.
  
  virtual task finish_item(ovm_sequence_item item, int set_priority = -1);
    item.m_finish_item(item.get_sequencer(), this, set_priority);
  endtask // finish_item


  // Function- m_start_item
  //
  // Internal method.
  
  virtual task m_start_item(ovm_sequencer_base sequencer_ptr, ovm_sequence_item sequence_ptr,
                            int set_priority);
    ovm_sequence_base this_seq;
    ovm_sequencer_base target_seqr;
    
    target_seqr = this.get_sequencer();
    if (!$cast(this_seq, sequence_ptr))
      ovm_report_fatal ("CASTFL", "start_item failed to cast sequence_ptr to sequence type", OVM_NONE);
    
    if (target_seqr == null) begin
      if (sequencer_ptr == null) begin
        ovm_report_fatal("STRITM", "sequence_item has null sequencer", OVM_NONE);
      end else begin
        target_seqr  = sequencer_ptr;
        set_use_sequence_info(1);
        set_sequencer(sequencer_ptr);
        set_parent_sequence(this_seq);
        reseed();
      end
    end
    
    target_seqr.wait_for_grant(this_seq, set_priority);
`ifdef INCA
    void'(target_seqr.begin_tr(this, "aggregate items"));
`else // QUESTA
    void'(target_seqr.begin_tr(this, "aggregate_items"));
`endif // INCA-QUESTA
    sequence_ptr.pre_do(1);
  endtask  


  // Function- m_finish_item
  //
  // Internal method.
  
  virtual task m_finish_item(ovm_sequencer_base sequencer_ptr, ovm_sequence_item sequence_ptr, int set_priority = -1);
    ovm_sequence_base this_seq;
    ovm_sequencer_base target_seqr;

    target_seqr = this.get_sequencer();
    if (!$cast(this_seq, sequence_ptr))
       ovm_report_fatal ("CASTFL", "finish_item failed to cast sequence_ptr to sequence type", OVM_NONE);
    sequence_ptr.mid_do(this);
    target_seqr.send_request(this_seq, this);
    target_seqr.wait_for_item_done(this_seq, -1);
    target_seqr.end_tr(this);

    sequence_ptr.post_do(this);
  endtask // m_finish_item


  // Function- get_full_name
  //
  // Internal method; overrides must follow same naming convention

  function string get_full_name();
    if(m_parent_sequence != null) 
      get_full_name = {m_parent_sequence.get_full_name(), "."};
    else if(m_sequencer!=null)
      get_full_name = {m_sequencer.get_full_name(), "."};
    if(get_name() != "") 
      get_full_name = {get_full_name, get_name()};
    else begin
      get_full_name = {get_full_name, "_item"};
    end
  endfunction


  // Function: get_root_sequence_name
  //
  // Provides the name of the root sequence (the top-most parent sequence).

  function string get_root_sequence_name();
    ovm_sequence_base root_seq;
    root_seq = get_root_sequence();
    if (root_seq == null)
      return "";
    else
      return root_seq.get_name();
  endfunction


  // Function- m_set_p_sequencer
  //
  // Internal method

  virtual function void m_set_p_sequencer();
    return;
  endfunction  


  // Function: get_root_sequence
  //
  // Provides a reference to the root sequence (the top-most parent sequence).

  function ovm_sequence_base get_root_sequence();
    ovm_sequence_item root_seq_base;
    ovm_sequence_base root_seq;
    root_seq_base = this;
    while(1) begin
      if(root_seq_base.get_parent_sequence()!=null) begin
        root_seq_base = root_seq_base.get_parent_sequence();
        $cast(root_seq, root_seq_base);
      end
      else
        return root_seq;
    end
  endfunction


  // Function: get_sequence_path
  //
  // Provides a string of names of each sequence in the full hierarchical
  // path. A "." is used as the separator between each sequence.

  function string get_sequence_path();
    ovm_sequence_item this_item;
    string seq_path;
    this_item = this;
    seq_path = this.get_name();
    while(1) begin
      if(this_item.get_parent_sequence()!=null) begin
        this_item = this_item.get_parent_sequence();
        seq_path = {this_item.get_name(), ".", seq_path};
      end
      else
        return seq_path;
    end
  endfunction


  // Function- do_print
  //
  // Internal method

  function void do_print (ovm_printer printer);
    string temp_str0, temp_str1;
    int depth = get_depth();
    super.do_print(printer);
    if(print_sequence_info || m_use_sequence_info) begin
      printer.print_field("depth", depth, $bits(depth), OVM_DEC, ".", "int");
      if(m_parent_sequence != null) begin
        temp_str0 = m_parent_sequence.get_name();
        temp_str1 = m_parent_sequence.get_full_name();
      end
      printer.print_string("parent sequence (name)", temp_str0);
      printer.print_string("parent sequence (full name)", temp_str1);
      temp_str1 = "";
      if(m_sequencer != null) begin
        temp_str1 = m_sequencer.get_full_name();
      end
      printer.print_string("sequencer", temp_str1);
    end
  endfunction


  //----------------------------------------------------------------------------
  // Deprecated Methods
  // 
  // These methods, which are sequence-centric, were moved to ovm_sequence_base.
  //----------------------------------------------------------------------------

  function void set_parent_seq(ovm_sequence_base parent);
    static bit issued=0;
    if (!issued) begin
      issued=1;
      ovm_report_warning("deprecated",
        {"ovm_sequence_item::set_parent_seq() has been deprecated and ",
        "replaced by set_parent_sequence()"});
    end
    set_parent_sequence(parent);
  endfunction

  function ovm_sequence_base get_parent_seq();
    static bit issued=0;
    if (!issued) begin
      issued=1;
      ovm_report_warning("deprecated",
        {"ovm_sequence_item::get_parent_seq() has been deprecated and ",
        "replaced by get_parent_sequence()"});
    end
    return(get_parent_sequence());
  endfunction // ovm_sequence_base

  virtual task pre_do(bit is_item);
    return;
  endtask // pre_body

  virtual task body();
    return;
  endtask  

  virtual function void mid_do(ovm_sequence_item this_item);
    return;
  endfunction
  
  virtual function void post_do(ovm_sequence_item this_item);
    return;
  endfunction

  virtual task wait_for_grant(int item_priority = -1, bit  lock_request = 0);
    return;
  endtask

  virtual function void send_request(ovm_sequence_item request, bit rerandomize = 0);
    return;
  endfunction

  virtual task wait_for_item_done(int transaction_id = -1);
    return;
  endtask // wait_for_item_done

endclass
`endif 
