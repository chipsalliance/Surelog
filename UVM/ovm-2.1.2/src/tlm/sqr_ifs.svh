// $Id: sqr_ifs.svh,v 1.6 2009/10/30 15:29:22 jlrose Exp $
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


`define SEQ_ITEM_TASK_ERROR "Sequencer interface task not implemented"
`define SEQ_ITEM_FUNCTION_ERROR "Sequencer interface function not implemented"

//------------------------------------------------------------------------------
//
// CLASS: sqr_if_base #(REQ,RSP)
//
// This class defines an interface for sequence drivers to communicate with
// sequencers. The driver requires the interface via a port, and the sequencer
// implements it and provides it via an export.
//
//------------------------------------------------------------------------------

virtual class sqr_if_base #(type T1=ovm_object, T2=T1);

  // Task: get_next_item
  //
  // Retrieves the next available item from a sequence.  The call will block
  // until an item is available.  The following steps occur on this call:
  //
  // 1 - Arbitrate among requesting, unlocked, relevant sequences - choose the
  //     highest priority sequence based on the current sequencer arbitration
  //     mode. If no sequence is available, wait for a requesting unlocked
  //     relevant sequence,  then re-arbitrate.
  // 2 - The chosen sequence will return from wait_for_grant
  // 3 - The chosen sequence pre_do is called
  // 4 - The chosen sequence item is randomized
  // 5 - The chosen sequence post_do is called
  // 6 - Return with a reference to the item
  //
  // Once get_next_item is called, item_done must be called to indicate the
  // completion of the request to the sequencer.  This will remove the request
  // item from the sequencer fifo.

  virtual task get_next_item(output T1 t);
    ovm_report_error("get_next_item", `SEQ_ITEM_TASK_ERROR, OVM_NONE);
  endtask
 

  // Task: try_next_item
  //
  // Retrieves the next available item from a sequence if one is available.
  // Otherwise, the function returns immediately with request set to null. 
  // The following steps occur on this call:
  //
  // 1 - Arbitrate among requesting, unlocked, relevant sequences - choose the
  //     highest priority sequence based on the current sequencer arbitration
  //     mode. If no sequence is available, return null.
  // 2 - The chosen sequence will return from wait_for_grant
  // 3 - The chosen sequence pre_do is called
  // 4 - The chosen sequence item is randomized
  // 5 - The chosen sequence post_do is called
  // 6 - Return with a reference to the item
  //
  // Once try_next_item is called, item_done must be called to indicate the
  // completion of the request to the sequencer.  This will remove the request
  // item from the sequencer fifo.

  virtual task try_next_item(output T1 t);
    ovm_report_error("try_next_item", `SEQ_ITEM_TASK_ERROR, OVM_NONE);
  endtask


  // Function: item_done
  //
  // Indicates that the request is completed to the sequencer.  Any 
  // wait_for_item_done calls made by a sequence for this item will return.
  //
  // The current item is removed from the sequencer fifo.
  //
  // If a response item is provided, then it will be sent back to the requesting
  // sequence. The response item must have it's sequence ID and transaction ID
  // set correctly, using the set_id_info method:
  //
  //|  rsp.set_id_info(req);
  //
  // Before item_done is called, any calls to peek will retrieve the current
  // item that was obtained by get_next_item.  After item_done is called, peek
  // will cause the sequencer to arbitrate for a new item.

  virtual function void item_done(input T2 t = null);
    ovm_report_error("item_done", `SEQ_ITEM_FUNCTION_ERROR, OVM_NONE);
  endfunction

  
  // Task: wait_for_sequences
  //
  // Waits for a sequence to have a new item available. The default
  // implementation in the sequencer delays pound_zero_count delta cycles.
  // (This variable is defined in ovm_sequencer_base.) User-derived sequencers
  // may override its wait_for_sequences implementation to perform some other
  // application-specific implementation.

  virtual task wait_for_sequences();
    ovm_report_error("wait_for_sequences", `SEQ_ITEM_TASK_ERROR, OVM_NONE);
  endtask


  // Function: has_do_available
  //
  // Indicates whether a sequence item is available for immediate processing.
  // Implementations should return 1 if an item is available, 0 otherwise. 

  virtual function bit has_do_available();
    ovm_report_error("has_do_available", `SEQ_ITEM_FUNCTION_ERROR, OVM_NONE);
    return 0;
  endfunction


  //-----------------------
  // tlm_blocking_slave_if
  //-----------------------

  // Task: get
  //
  // Retrieves the next available item from a sequence.  The call blocks until
  // an item is available. The following steps occur on this call:
  //
  // 1 - Arbitrate among requesting, unlocked, relevant sequences - choose the
  //     highest priority sequence based on the current sequencer arbitration
  //     mode. If no sequence is available, wait for a requesting unlocked
  //     relevant sequence, then re-arbitrate.
  // 2 - The chosen sequence will return from wait_for_grant
  // 3 - The chosen sequence <pre_do> is called
  // 4 - The chosen sequence item is randomized
  // 5 - The chosen sequence post_do is called
  // 6 - Indicate item_done to the sequencer
  // 7 - Return with a reference to the item
  //
  // When get is called, item_done may not be called.  A new item can be
  // obtained by calling get again, or a response may be sent using either
  // put, or rsp_port.write.

  virtual task get(output T1 t);
    ovm_report_error("get", `SEQ_ITEM_TASK_ERROR, OVM_NONE);
  endtask

  // Task: peek
  //
  // Returns the current request item if one is in the sequencer fifo.  If no
  // item is in the fifo, then the call will block until the sequencer has a new
  // request. The following steps will occur if the sequencer fifo is empty:
  //
  // 1 - Arbitrate among requesting, unlocked, relevant sequences - choose the
  // highest priority sequence based on the current sequencer arbitration mode.
  // If no sequence is available, wait for a requesting unlocked relevant
  // sequence, then re-arbitrate.
  //
  // 2 - The chosen sequence will return from wait_for_grant
  // 3 - The chosen sequence pre_do is called
  // 4 - The chosen sequence item is randomized
  // 5 - The chosen sequence post_do is called
  //
  // Once a request item has been retrieved and is in the sequencer fifo,
  // subsequent calls to peek will return the same item.  The item will stay in
  // the fifo until either get or item_done is called.

  virtual task peek(output T1 t);
    ovm_report_error("peek", `SEQ_ITEM_TASK_ERROR, OVM_NONE);
  endtask


  // Task: put
  //
  // Sends a response back to the sequence that issued the request. Before the
  // response is put, it must have it's sequence ID and transaction ID set to
  // match the request.  This can be done using the set_id_info call:
  //
  //   rsp.set_id_info(req);
  //
  // This task will not block. The response will be put into the sequence
  // response_queue or it will be sent to the sequence response handler.

  virtual task put(input T2 t);
    ovm_report_error("put", `SEQ_ITEM_TASK_ERROR, OVM_NONE);
  endtask


  // Function- put_response
  //
  // Internal method.

  virtual function void put_response(input T2 t);
    ovm_report_error("put_response", `SEQ_ITEM_FUNCTION_ERROR, OVM_NONE);
  endfunction

endclass
