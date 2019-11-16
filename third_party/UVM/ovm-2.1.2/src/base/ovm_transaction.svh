//
//-----------------------------------------------------------------------------
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
//-----------------------------------------------------------------------------

`ifndef OVM_TRANSACTION_SVH
`define OVM_TRANSACTION_SVH

typedef class ovm_event;
typedef class ovm_event_pool;
typedef class ovm_component;
    
//------------------------------------------------------------------------------
//
// CLASS: ovm_transaction
//
// The ovm_transaction class is the root base class for OVM transactions.
// Inheriting all the methods of ovm_object, ovm_transaction adds a timing and
// recording interface.
//
//------------------------------------------------------------------------------
    
virtual class ovm_transaction extends ovm_object;

  // Function: new
  //
  // Creates a new transaction object. The name is the instance name of the
  // transaction. If not supplied, then the object is unnamed.
  
  extern function new (string name="", ovm_component initiator=null);



  // Function: accept_tr
  //
  // Calling accept_tr indicates that the transaction has been accepted for
  // processing by a consumer component, such as an ovm_driver. With some
  // protocols, the transaction may not be started immediately after it is
  // accepted. For example, a bus driver may have to wait for a bus grant
  // before starting the transaction.
  //
  // This function performs the following actions:
  //
  // - The transaction's internal accept time is set to the current simulation
  //   time, or to accept_time if provided and non-zero. The accept_time may be
  //   any time, past or future.
  //
  // - The transaction's internal accept event is triggered. Any processes
  //   waiting on the this event will resume in the next delta cycle. 
  //
  // - The do_accept_tr method is called to allow for any post-accept
  //   action in derived classes.

  extern function void accept_tr (time accept_time=0);

  
  // Function: do_accept_tr
  //
  // This user-definable callback is called by accept_tr just before the accept
  // event is triggered. Implementations should call super.do_accept_tr to
  // ensure correct operation.

  extern virtual protected function void do_accept_tr ();


  // Function: begin_tr
  //
  // This function indicates that the transaction has been started and is not
  // the child of another transaction. Generally, a consumer component begins
  // execution of the transactions it receives. 
  //
  // This function performs the following actions:
  //
  // - The transaction's internal start time is set to the current simulation
  //   time, or to begin_time if provided and non-zero. The begin_time may be
  //   any time, past or future, but should not be less than the accept time.
  //
  // - If recording is enabled, then a new database-transaction is started with
  //   the same begin time as above. The record method inherited from ovm_object
  //   is then called, which records the current property values to this new
  //   transaction.
  //
  // - The do_begin_tr method is called to allow for any post-begin action in
  //   derived classes.
  //
  // - The transaction's internal begin event is triggered. Any processes
  //   waiting on this event will resume in the next delta cycle. 
  //
  // The return value is a transaction handle, which is valid (non-zero) only if
  // recording is enabled. The meaning of the handle is implementation specific.


  extern function integer begin_tr (time begin_time=0);

  
  // Function: begin_child_tr
  //
  // This function indicates that the transaction has been started as a child of
  // a parent transaction given by parent_handle. Generally, a consumer
  // component begins execution of the transactions it receives.
  //
  // The parent handle is obtained by a previous call to begin_tr or
  // begin_child_tr. If the parent_handle is invalid (=0), then this function
  // behaves the same as begin_tr. 
  //
  // This function performs the following actions:
  //
  // - The transaction's internal start time is set to the current simulation
  //   time, or to begin_time if provided and non-zero. The begin_time may be
  //   any time, past or future, but should not be less than the accept time.
  //
  // - If recording is enabled, then a new database-transaction is started with
  //   the same begin time as above. The record method inherited from ovm_object
  //   is then called, which records the current property values to this new
  //   transaction. Finally, the newly started transaction is linked to the
  //   parent transaction given by parent_handle.
  //
  // - The <do_begin_tr> method is called to allow for any post-begin
  //   action in derived classes.
  //
  // - The transaction's internal begin event is triggered. Any processes
  //   waiting on this event will resume in the next delta cycle. 
  //
  // The return value is a transaction handle, which is valid (non-zero) only if
  // recording is enabled. The meaning of the handle is implementation specific.

  extern function integer begin_child_tr (time begin_time=0, 
                                          integer parent_handle=0);


  // Function: do_begin_tr
  //
  // This user-definable callback is called by begin_tr and begin_child_tr just
  // before the begin event is triggered. Implementations should call
  // super.do_begin_tr to ensure correct operation.

  extern virtual protected function void do_begin_tr ();


  // Function: end_tr
  //
  // This function indicates that the transaction execution has ended.
  // Generally, a consumer component ends execution of the transactions it
  // receives. 
  //
  // This function performs the following actions:
  //
  // - The transaction's internal end time is set to the current simulation
  //   time, or to end_time if provided and non-zero. The end_time may be any
  //   time, past or future, but should not be less than the begin time.
  //
  // - If recording is enabled and a database-transaction is currently active,
  //   then the record method inherited from ovm_object is called, which records
  //   the final property values. The transaction is then ended. If free_handle
  //   is set, the transaction is released and can no longer be linked to (if
  //   supported by the implementation).
  //
  // - The <do_end_tr> method is called to allow for any post-end
  //   action in derived classes.
  //
  // - The transaction's internal end event is triggered. Any processes waiting
  //   on this event will resume in the next delta cycle. 

  extern function void end_tr (time end_time=0, bit free_handle=1);


  // Function: do_end_tr
  //
  // This user-definable callback is called by end_tr just before the end event
  // is triggered. Implementations should call super.do_end_tr to ensure correct
  // operation.

  extern virtual protected function void do_end_tr ();


  // Function: get_tr_handle
  //
  // Returns the handle associated with the transaction, as set by a previous
  // call to begin_child_tr or begin_tr with transaction recording enabled.

  extern function integer get_tr_handle ();

  
  // Function: disable_recording
  //
  // Turns off recording for the transaction stream. This method does not
  // effect a component's recording streams.

  extern function void disable_recording ();


  // Function: enable_recording
  //
  // Turns on recording to the stream specified by stream, whose interpretation
  // is implementation specific.
  //
  // If transaction recording is on, then a call to record is made when the
  // transaction is started and when it is ended.

  extern function void enable_recording (string stream);


  // Function: is_recording_enabled
  //
  // Returns 1 if recording is currently on, 0 otherwise.

  extern function bit is_recording_enabled();

  
  // Function: is_active
  //
  // Returns 1 if the transaction has been started but has not yet been ended.
  // Returns 0 if the transaction has not been started.

  extern function bit is_active ();


  // Function: get_event_pool
  //
  // Returns the event pool associated with this transaction. 
  //
  // By default, the event pool contains the events: begin, accept, and end.
  // Events can also be added by derivative objects. See ovm_event_pool for
  // more information.

  extern function ovm_event_pool get_event_pool ();


  // Function: set_initiator
  //
  // Sets initiator as the initiator of this transaction. 
  //
  // The initiator can be the component that produces the transaction. It can
  // also be the component that started the transaction. This or any other
  // usage is up to the transaction designer.

  extern function void set_initiator (ovm_component initiator);

  
  // Function: get_initiator
  //
  // Returns the component that produced or started the transaction, as set by
  // a previous call to set_initiator.

  extern function ovm_component get_initiator ();


  // Function: get_accept_time

  extern function time   get_accept_time    ();

  // Function: get_begin_time

  extern function time   get_begin_time     ();

  // Function: get_end_time
  //
  // Returns the time at which this transaction was accepted, begun, or ended, 
  // as by a previous call to accept_tr, begin_tr, begin_child_tr, or end_tr.

  extern function time   get_end_time       ();


  // Function: set_transaction_id
  //
  // Sets this transaction's numeric identifier to id. If not set via this
  // method, the transaction ID defaults to -1. 
  //
  // When using sequences to generate stimulus, the transaction ID is used along
  // with the sequence ID to route responses in sequencers and to correlate
  // responses to requests.

  extern function void set_transaction_id(integer id);


  // Function: get_transaction_id
  //
  // Returns this transaction's numeric identifier, which is -1 if not set
  // explicitly by set_transaction_id.
  //
  // When using sequences to generate stimulus, the transaction ID is used along
  // with the sequence ID to route responses in sequencers and to correlate
  // responses to requests.

  extern function integer get_transaction_id();

  //----------------------------------------------------------------------------
  //
  // Internal methods properties; do not use directly
  //
  //----------------------------------------------------------------------------

  //Override data control methods for internal properties
  extern virtual function void do_print  (ovm_printer printer);
  extern virtual function void do_record (ovm_recorder recorder);
  extern virtual function void do_copy   (ovm_object rhs);


  extern protected function integer m_begin_tr (time    begin_time=0, 
                                                integer parent_handle=0,
                                                bit     has_parent=0);

  local integer m_transaction_id = 0;

  local time    begin_time=-1;
  local time    end_time=-1;
  local time    accept_time=-1;

  local ovm_component initiator;
  local integer       stream_handle;
  local integer       tr_handle;      
  local bit           record_enable = 0;

  ovm_event_pool events = new;

endclass

`endif // OVM_TRANSACTION_SVH
