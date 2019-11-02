// $Id: sqr_connections.svh,v 1.5 2008/08/22 16:09:36 jlrose Exp $
//-----------------------------------------------------------------------------
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
//-----------------------------------------------------------------------------


`define SEQ_ITEM_PULL_IMP(imp, REQ, RSP, req_arg, rsp_arg) \
  task get_next_item(output REQ req_arg); imp.get_next_item(req_arg); endtask \
  task try_next_item(output REQ req_arg); imp.try_next_item(req_arg); endtask \
  function void item_done(input RSP rsp_arg = null); imp.item_done(rsp_arg); endfunction \
  task wait_for_sequences(); imp.wait_for_sequences(); endtask \
  function bit has_do_available(); return imp.has_do_available(); endfunction \
  function void put_response(input RSP rsp_arg); imp.put_response(rsp_arg); endfunction \
  task get(output REQ req_arg); imp.get(req_arg); endtask \
  task peek(output REQ req_arg); imp.peek(req_arg); endtask \
  task put(input RSP rsp_arg); imp.put(rsp_arg); endtask

//  function void connect_if(ovm_port_base #(sqr_if_base#(REQ, RSP)) seq_item_port); endtask

// `define SEQ_ITEM_UNI_PULL_IMP(imp, T, arg) \
//   task get_next_item(output T arg); imp.get_next_item(arg); endtask \
//   task try_next_item(output T arg); imp.try_next_item(arg); endtask \
//   function void item_done(input T arg = null); imp.item_done(arg); endfunction \
//   task wait_for_sequences(); imp.wait_for_sequences(); endtask \
//   function bit has_do_available(); return imp.has_do_available(); endfunction \
//   task get(output T arg); imp.get(arg); endtask \
//   task peek(output T arg); imp.peek(arg); endtask

// `define SEQ_ITEM_PUSH_IMP(imp, T, arg) \
//   task put(input T arg); imp.put(arg); endtask


//-----------------------------------------------------------------------------
//
// CLASS: ovm_seq_item_pull_port #(REQ,RSP)
//
// OVM provides a port, export, and imp connector for use in sequencer-driver
// communication. All have standard port connector constructors, except that
// ovm_seq_item_pull_port's default min_size argument is 0; it can be left
// unconnected.
//
//-----------------------------------------------------------------------------

class ovm_seq_item_pull_port #(type REQ=int, type RSP=REQ)
  extends ovm_port_base #(sqr_if_base #(REQ, RSP));
  `OVM_SEQ_PORT(`SEQ_ITEM_PULL_MASK, "ovm_seq_item_pull_port")
  `SEQ_ITEM_PULL_IMP(this.m_if, REQ, RSP, t, t)

  bit print_enabled = 0;
    
  // provided for backwards compatibility
  function void connect_if(ovm_port_base#(sqr_if_base#(REQ,RSP)) provider);
    super.connect(provider);
    ovm_report_warning("deprecated",
                       "ovm_seq_item_pull_port.connect_if has been deprecated");
  endfunction // void

endclass


//-----------------------------------------------------------------------------
//
// CLASS: ovm_seq_item_pull_export #(REQ,RSP)
//
// This export type is used in sequencer-driver communication. It has the
// standard constructor for exports.
//
//-----------------------------------------------------------------------------

class ovm_seq_item_pull_export #(type REQ=int, type RSP=REQ)
  extends ovm_port_base #(sqr_if_base #(REQ, RSP));
  `OVM_EXPORT_COMMON(`SEQ_ITEM_PULL_MASK, "ovm_seq_item_pull_export")
  `SEQ_ITEM_PULL_IMP(this.m_if, REQ, RSP, t, t)
endclass


//-----------------------------------------------------------------------------
//
// CLASS: ovm_seq_item_pull_imp #(REQ,RSP,IMP)
//
// This imp type is used in sequencer-driver communication. It has the
// standard constructor for imp-type ports.
//
//-----------------------------------------------------------------------------

class ovm_seq_item_pull_imp #(type REQ=int, type RSP=REQ, type IMP=int)
  extends ovm_port_base #(sqr_if_base #(REQ, RSP));
  `OVM_IMP_COMMON(`SEQ_ITEM_PULL_MASK, "ovm_seq_item_pull_imp",IMP)
  `SEQ_ITEM_PULL_IMP(m_imp, REQ, RSP, t, t)

  // provided for backwards compatibility of connect_if call
  function void connect_if(ovm_port_base#(sqr_if_base#(REQ,RSP)) provider);
    provider.connect(this);
    ovm_report_warning("deprecated",
                       "ovm_seq_item_pull_imp.connect_if has been deprecated");
  endfunction // void

endclass

// Section: end
