// $Id: ovm_push_driver.svh,v 1.9 2009/10/30 15:29:22 jlrose Exp $
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

//------------------------------------------------------------------------------
//
// CLASS: ovm_push_driver #(REQ,RSP)
//
// Base class for a driver that passively receives transactions, i.e. does not
// initiate requests transactions. Also known as ~push~ mode. Its ports are
// typically connected to the corresponding ports in a push sequencer as follows:
//
//|  push_sequencer.req_port.connect(push_driver.req_export);
//|  push_driver.rsp_port.connect(push_sequencer.rsp_export);
//
// The ~rsp_port~ needs connecting only if the driver will use it to write
// responses to the analysis export in the sequencer.
//
//------------------------------------------------------------------------------

class ovm_push_driver #(type REQ=ovm_sequence_item,
                        type RSP=REQ) extends ovm_component;

  // Port: req_export
  //
  // This export provides the blocking put interface whose default 
  // implementation produces an error. Derived drivers must override ~put~
  // with an appropriate implementation (and not call super.put). Ports
  // connected to this export will supply the driver with transactions.

  ovm_blocking_put_imp #(REQ, ovm_push_driver #(REQ,RSP)) req_export;

  // Port: rsp_port
  //
  // This analysis port is used to send response transactions back to the
  // originating sequencer.

  ovm_analysis_port #(RSP) rsp_port;

  REQ req;
  RSP rsp;

  // Function: new
  //
  // Creates and initializes an instance of this class using the normal
  // constructor arguments for <ovm_component>: ~name~ is the name of the
  // instance, and ~parent~ is the handle to the hierarchical parent, if any.

  function new (string name, ovm_component parent);
    super.new(name, parent);
    req_export = new("req_export", this);
    rsp_port   = new("rsp_port", this);
  endfunction

  function void check_port_connections();
    if (req_export.size() != 1)
    ovm_report_fatal("Connection Error",
                     $psprintf("Must connect to seq_item_port(%0d)",
                               req_export.size()), OVM_NONE);
  endfunction
  
  virtual function void end_of_elaboration();
    check_port_connections();
  endfunction
  
  virtual task put(REQ item);
    ovm_report_fatal("OVM_PUSH_DRIVER", "Put task for push driver is not implemented", OVM_NONE);
  endtask

  const static string type_name = "ovm_push_driver #(REQ,RSP)";

  virtual function string get_type_name ();
    return type_name;
  endfunction

endclass

