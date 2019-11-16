//
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

`include "base/ovm_transaction.svh"

// new
// ---

function ovm_transaction::new (string name="", 
                               ovm_component initiator = null);

  super.new(name);
  this.initiator = initiator;
  m_transaction_id = -1;
  ///events = new;
endfunction // ovm_transaction


// set_transaction_id
function void ovm_transaction::set_transaction_id(integer id);
    m_transaction_id = id;
endfunction

// get_transaction_id
function integer ovm_transaction::get_transaction_id();
    return (m_transaction_id);
endfunction

// set_initiator
// ------------

function void ovm_transaction::set_initiator(ovm_component initiator);
  this.initiator = initiator;
endfunction

// get_initiator
// ------------

function ovm_component ovm_transaction::get_initiator();
  return initiator;
endfunction

// get_event_pool
// --------------

function ovm_event_pool ovm_transaction::get_event_pool();
  return events;
endfunction


// is_active
// ---------

function bit ovm_transaction::is_active();
  return (tr_handle != 0);
endfunction


// get_begin_time
// --------------

function time ovm_transaction::get_begin_time ();
  return begin_time;
endfunction


// get_end_time
// ------------

function time ovm_transaction::get_end_time ();
  return end_time;
endfunction


// get_accept_time
// ---------------

function time ovm_transaction::get_accept_time ();
  return accept_time;
endfunction


// do_accept_tr
// -------------

function void ovm_transaction::do_accept_tr();
  return;
endfunction


// do_begin_tr
// ------------

function void ovm_transaction::do_begin_tr();
  return;
endfunction


// do_end_tr
// ----------

function void ovm_transaction::do_end_tr();
  return;
endfunction

// do_print
// --------

function void ovm_transaction::do_print (ovm_printer printer);
  string str;
  ovm_component tmp_initiator; //work around $swrite bug
  super.do_print(printer);
  if(accept_time != -1)
    printer.print_time("accept_time", accept_time);
  if(begin_time != -1)
    printer.print_time("begin_time", begin_time);
  if(end_time != -1)
    printer.print_time("end_time", end_time);
  if(initiator != null) begin
    tmp_initiator = initiator;
`ifdef INCA
    $swrite(str,"@%0d", tmp_initiator);
`else
`endif
    printer.print_generic("initiator", initiator.get_type_name(), -1, str);
  end
endfunction

function void ovm_transaction::do_copy (ovm_object rhs);
  ovm_transaction txn;
  super.do_copy(rhs);
  if(rhs == null) return;
  if(!$cast(txn, rhs) ) return;

  accept_time = txn.accept_time;
  begin_time = txn.begin_time;
  end_time = txn.end_time;
  initiator = txn.initiator;
  stream_handle = txn.stream_handle;
  tr_handle = txn.tr_handle;
  record_enable = txn.record_enable;
endfunction  

// do_record
// ---------

function void ovm_transaction::do_record (ovm_recorder recorder);
  string s;
  super.do_record(recorder);
  if(accept_time != -1)
    void'(m_do_data ("accept_time", accept_time, 0, OVM_RECORD, 
                     $bits(accept_time), 0));
  if(initiator != null) 
    m_record_field_object("initiator", initiator, 
                          ovm_auto_options_object.recorder, 0);
endfunction

// get_tr_handle
// ---------

function integer ovm_transaction::get_tr_handle ();
  return tr_handle;
endfunction


// disable_recording
// -----------------

function void ovm_transaction::disable_recording ();
  record_enable = 0;
endfunction


// enable_recording
// ----------------

function void ovm_transaction::enable_recording (string stream);
  string scope;
  int lastdot;
  for(lastdot=stream.len()-1; lastdot>0; --lastdot)
    if(stream[lastdot] == ".") break;

  if(lastdot) begin
    scope = stream.substr(0, lastdot-1);
    stream = stream.substr(lastdot+1, stream.len()-1);
  end
  this.stream_handle = ovm_create_fiber(stream, "TVM", scope);
  record_enable = 1;
endfunction


// is_recording_enabled
// --------------------

function bit ovm_transaction::is_recording_enabled ();
  return record_enable;
endfunction


// accept_tr
// ---------

function void ovm_transaction::accept_tr (time accept_time = 0);
  ovm_event e;

  if(accept_time != 0)
    this.accept_time = accept_time;
  else
    this.accept_time = $time;

  do_accept_tr();
  e = events.get("accept");

  if(e!=null) 
    e.trigger();
endfunction

// begin_tr
// -----------

function integer ovm_transaction::begin_tr (time begin_time=0); 
  return m_begin_tr(begin_time, 0, 0);
endfunction

// begin_child_tr
// --------------

//Use a parent handle of zero to link to the parent after begin
function integer ovm_transaction::begin_child_tr (time begin_time=0,
                                                  integer parent_handle=0); 
  return m_begin_tr(begin_time, parent_handle, 1);
endfunction

// m_begin_tr
// -----------

function integer ovm_transaction::m_begin_tr (time begin_time=0, 
                                              integer parent_handle=0, 
                                              bit has_parent=0);
  ovm_event e;

  if(begin_time != 0)
    this.begin_time = begin_time;
  else
    this.begin_time = $time;
   
  // May want to establish predecessor/successor relation 
  // (don't free handle until then)
  if(record_enable) begin 

    if(ovm_check_handle_kind("Transaction", tr_handle)==1)
      end_tr(); 

    if(!has_parent)
      tr_handle = ovm_begin_transaction("Begin_No_Parent, Link", 
                    stream_handle, get_type_name(),"","",begin_time);
    else begin
      tr_handle = ovm_begin_transaction("Begin_End, Link", 
                    stream_handle, get_type_name(),"","",begin_time);
      if(parent_handle)
        ovm_link_transaction(parent_handle, tr_handle, "child");
    end

    ovm_default_recorder.tr_handle = tr_handle;
    record(ovm_default_recorder);

    if(ovm_check_handle_kind("Transaction", tr_handle)!=1)
      $display("tr handle %0d not valid!",tr_handle);

  end
  else 
    tr_handle = 0;

  e = events.get("begin");

  do_begin_tr(); //execute callback before event trigger

  if(e!=null) 
    e.trigger();
 
  return tr_handle;
endfunction


// end_tr
// ------

function void ovm_transaction::end_tr (time end_time=0, bit free_handle=1);
  ovm_event e;

  if(end_time != 0)
    this.end_time = end_time;
  else
    this.end_time = $time;

  do_end_tr(); // Callback prior to actual ending of transaction

  if(is_active()) begin
    ovm_default_recorder.tr_handle = tr_handle;
    record(ovm_default_recorder);
  
    ovm_end_transaction(tr_handle,end_time);

    if(free_handle && ovm_check_handle_kind("Transaction", tr_handle)==1) 
    begin  
      ovm_free_transaction_handle(tr_handle);
    end
    tr_handle = 0;
  end

  e = events.get("end");

  if(e!=null) 
    e.trigger();
endfunction







