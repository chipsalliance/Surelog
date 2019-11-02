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

//-----------------------------------------------------------------------------
//
// Title: TLM Implementation Port Declaration Macros
//
// The TLM implemenation declaration macros provide a way for an implementer
// to provide multiple implemenation ports of the same implementation 
// interface. When an implementation port is defined using the built-in
// set of imps, there must be exactly one implementation of the interface.
//
// For example, if a component needs to provide a put implemenation then
// it would have an implementation port defined like:
//
//| class mycomp extends ovm_component;
//|   ovm_put_imp#(data_type, mycomp) put_imp;
//|   ...
//|   virtual task put (data_type t);
//|     ...
//|   endtask
//| endclass
//
// There are times, however, when you need more than one implementation for
// for an interface. This set of declarations allow you to easily create
// a new implemenation class to allow for multiple implementations. Although
// the new implemenation class is a different class, it can be bound to
// the same types of exports and ports as the original class. Extending
// the put example above, lets say that mycomp needs to provide two put
// implementation ports. In that case, you would do something like:
//
//| //Define two new put interfaces which are compatible with ovm_put_ports
//| //and ovm_put_exports.
//|
//| `ovm_put_imp_decl(_1)
//| `ovm_put_imp_decl(_2)
//|
//| class my_put_imp#(type T=int) extends ovm_component;
//|    ovm_put_imp_1#(T) put_imp1;
//|    ovm_put_imp_2#(T) put_imp2;
//|    ...
//|    function void put_1 (input T t);
//|      //puts comming into put_imp1
//|      ...
//|    endfunction
//|    function void put_2(input T t);
//|      //puts comming into put_imp2
//|      ...
//|    endfunction
//| endclass
//
// The important thing to note is that each `ovm_<interface>_imp_decl creates a 
// new class of type ovm_<interface>_imp<suffix>, where suffix is the input 
// argument to the macro. For this reason, you will typically want to put
// these macros in a seperate package to avoid collisions and to allow 
// sharing of the definitions.
//-----------------------------------------------------------------------------

// MACRO: `ovm_blocking_put_imp_decl
//
// Define the class ovm_blocking_put_impSFX for providing blocking put
// implementations.  ~SFX~ is the suffix for the new class type.

`define ovm_blocking_put_imp_decl(SFX) \
class ovm_blocking_put_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_BLOCKING_PUT_MASK,`"ovm_blocking_put_imp``SFX`",IMP) \
  `BLOCKING_PUT_IMP_SFX(SFX, m_imp, T, t) \
endclass

// MACRO: `ovm_nonblocking_put_imp_decl
//
// Define the class ovm_nonblocking_put_impSFX for providing non-blocking 
// put implementations.  ~SFX~ is the suffix for the new class type.

`define ovm_nonblocking_put_imp_decl(SFX) \
class ovm_nonblocking_put_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_NONBLOCKING_PUT_MASK,`"ovm_nonblocking_put_imp``SFX`",IMP) \
  `NONBLOCKING_PUT_IMP_SFX( SFX, m_imp, T, t) \
endclass

// MACRO: `ovm_put_imp_decl
//
// Define the class ovm_put_impSFX for providing both blocking and
// non-blocking put implementations.  ~SFX~ is the suffix for the new class
// type.

`define ovm_put_imp_decl(SFX) \
class ovm_put_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_PUT_MASK,`"ovm_put_imp``SFX`",IMP) \
  `BLOCKING_PUT_IMP_SFX(SFX, m_imp, T, t) \
  `NONBLOCKING_PUT_IMP_SFX(SFX, m_imp, T, t) \
endclass

// MACRO: `ovm_blocking_get_imp_decl
//
// Define the class ovm_blocking_get_impSFX for providing blocking get
// implementations.  ~SFX~ is the suffix for the new class type.

`define ovm_blocking_get_imp_decl(SFX) \
class ovm_blocking_get_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_BLOCKING_GET_MASK,`"ovm_blocking_get_imp``SFX`",IMP) \
  `BLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
endclass

// MACRO: `ovm_nonblocking_get_imp_decl
//
// Define the class ovm_nonblocking_get_impSFX for providing non-blocking 
// get implementations.  ~SFX~ is the suffix for the new class type.

`define ovm_nonblocking_get_imp_decl(SFX) \
class ovm_nonblocking_get_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_NONBLOCKING_GET_MASK,`"ovm_nonblocking_get_imp``SFX`",IMP) \
  `NONBLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
endclass

// MACRO: `ovm_get_imp_decl
//
// Define the class ovm_get_impSFX for providing both blocking and
// non-blocking get implementations.  ~SFX~ is the suffix for the new class
// type.

`define ovm_get_imp_decl(SFX) \
class ovm_get_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_GET_MASK,`"ovm_get_imp``SFX`",IMP) \
  `BLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
  `NONBLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
endclass

// MACRO: `ovm_blocking_peek_imp_decl
//
// Define the class ovm_blocking_peek_impSFX for providing blocking peek
// implementations.  ~SFX~ is the suffix for the new class type.

`define ovm_blocking_peek_imp_decl(SFX) \
class ovm_blocking_peek_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_BLOCKING_PEEK_MASK,`"ovm_blocking_peek_imp``SFX`",IMP) \
  `BLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
endclass 

// MACRO: `ovm_nonblocking_peek_imp_decl
//
// Define the class ovm_nonblocking_peek_impSFX for providing non-blocking 
// peek implementations.  ~SFX~ is the suffix for the new class type.

`define ovm_nonblocking_peek_imp_decl(SFX) \
class ovm_nonblocking_peek_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_NONBLOCKING_PEEK_MASK,`"ovm_nonblocking_peek_imp``SFX`",IMP) \
  `NONBLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
endclass

// MACRO: `ovm_peek_imp_decl
//
// Define the class ovm_peek_impSFX for providing both blocking and
// non-blocking peek implementations.  ~SFX~ is the suffix for the new class
// type.

`define ovm_peek_imp_decl(SFX) \
class ovm_peek_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_PEEK_MASK,`"ovm_peek_imp``SFX`",IMP) \
  `BLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
  `NONBLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
endclass


// MACRO: `ovm_blocking_get_peek_imp_decl
//
// Define the class ovm_blocking_get_peek_impSFX for providing the
// blocking get_peek implemenation.

`define ovm_blocking_get_peek_imp_decl(SFX) \
class ovm_blocking_get_peek_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_BLOCKING_GET_PEEK_MASK,`"ovm_blocking_get_peek_imp``SFX`",IMP) \
  `BLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
  `BLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
endclass

// MACRO: `ovm_nonblocking_get_peek_imp_decl
//
// Define the class ovm_nonblocking_get_peek_impSFX for providing non-blocking 
// get_peek implemenation.

`define ovm_nonblocking_get_peek_imp_decl(SFX) \
class ovm_nonblocking_get_peek_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_NONBLOCKING_GET_PEEK_MASK,`"ovm_nonblocking_get_peek_imp``SFX`",IMP) \
  `NONBLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
  `NONBLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
endclass


// MACRO: `ovm_get_peek_imp_decl
//
// Define the class ovm_get_peek_impSFX for providing both blocking and
// non-blocking get_peek implementations.  ~SFX~ is the suffix for the new class
// type.

`define ovm_get_peek_imp_decl(SFX) \
class ovm_get_peek_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_GET_PEEK_MASK,`"ovm_get_peek_imp``SFX`",IMP) \
  `BLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
  `NONBLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
  `BLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
  `NONBLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
endclass

// MACRO: `ovm_blocking_master_imp_decl
//
// Define the class ovm_blocking_master_impSFX for providing the
// blocking master implemenation.

`define ovm_blocking_master_imp_decl(SFX) \
class ovm_blocking_master_imp``SFX #(type REQ=int, type RSP=int, type IMP=int, \
                                     type REQ_IMP=IMP, type RSP_IMP=IMP) \
  extends ovm_port_base #(tlm_if_base #(REQ, RSP)); \
  typedef IMP     this_imp_type; \
  typedef REQ_IMP this_req_type; \
  typedef RSP_IMP this_rsp_type; \
  `OVM_MS_IMP_COMMON(`TLM_BLOCKING_MASTER_MASK,`"ovm_blocking_master_imp``SFX`") \
  \
  `BLOCKING_PUT_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  \
  `BLOCKING_GET_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  `BLOCKING_PEEK_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  \
endclass

// MACRO: `ovm_nonblocking_master_imp_decl
//
// Define the class ovm_nonblocking_master_impSFX for providing the
// non-blocking master implemenation.

`define ovm_nonblocking_master_imp_decl(SFX) \
class ovm_nonblocking_master_imp``SFX #(type REQ=int, type RSP=int, type IMP=int, \
                                   type REQ_IMP=IMP, type RSP_IMP=IMP) \
  extends ovm_port_base #(tlm_if_base #(REQ, RSP)); \
  typedef IMP     this_imp_type; \
  typedef REQ_IMP this_req_type; \
  typedef RSP_IMP this_rsp_type; \
  `OVM_MS_IMP_COMMON(`TLM_NONBLOCKING_MASTER_MASK,`"ovm_nonblocking_master_imp``SFX`") \
  \
  `NONBLOCKING_PUT_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  \
  `NONBLOCKING_GET_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  `NONBLOCKING_PEEK_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  \
endclass

// MACRO: `ovm_master_imp_decl
//
// Define the class ovm_master_impSFX for providing both blocking and
// non-blocking master implementations.  ~SFX~ is the suffix for the new class
// type.

`define ovm_master_imp_decl(SFX) \
class ovm_master_imp``SFX #(type REQ=int, type RSP=int, type IMP=int, \
                            type REQ_IMP=IMP, type RSP_IMP=IMP) \
  extends ovm_port_base #(tlm_if_base #(REQ, RSP)); \
  typedef IMP     this_imp_type; \
  typedef REQ_IMP this_req_type; \
  typedef RSP_IMP this_rsp_type; \
  `OVM_MS_IMP_COMMON(`TLM_MASTER_MASK,`"ovm_master_imp``SFX`") \
  \
  `BLOCKING_PUT_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  `NONBLOCKING_PUT_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  \
  `BLOCKING_GET_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  `BLOCKING_PEEK_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  `NONBLOCKING_GET_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  `NONBLOCKING_PEEK_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  \
endclass

// MACRO: `ovm_blocking_slave_imp_decl
//
// Define the class ovm_blocking_slave_impSFX for providing the
// blocking slave implemenation.

`define ovm_blocking_slave_imp_decl(SFX) \
class ovm_blocking_slave_imp``SFX #(type REQ=int, type RSP=int, type IMP=int, \
                                    type REQ_IMP=IMP, type RSP_IMP=IMP) \
  extends ovm_port_base #(tlm_if_base #(RSP, REQ)); \
  typedef IMP     this_imp_type; \
  typedef REQ_IMP this_req_type; \
  typedef RSP_IMP this_rsp_type; \
  `OVM_MS_IMP_COMMON(`TLM_BLOCKING_SLAVE_MASK,`"ovm_blocking_slave_imp``SFX`") \
  \
  `BLOCKING_PUT_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  \
  `BLOCKING_GET_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  `BLOCKING_PEEK_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  \
endclass

// MACRO: `ovm_nonblocking_slave_imp_decl
//
// Define the class ovm_nonblocking_slave_impSFX for providing the
// non-blocking slave implemenation.

`define ovm_nonblocking_slave_imp_decl(SFX) \
class ovm_nonblocking_slave_imp``SFX #(type REQ=int, type RSP=int, type IMP=int, \
                                       type REQ_IMP=IMP, type RSP_IMP=IMP) \
  extends ovm_port_base #(tlm_if_base #(RSP, REQ)); \
  typedef IMP     this_imp_type; \
  typedef REQ_IMP this_req_type; \
  typedef RSP_IMP this_rsp_type; \
  `OVM_MS_IMP_COMMON(`TLM_NONBLOCKING_SLAVE_MASK,`"ovm_nonblocking_slave_imp``SFX`") \
  \
  `NONBLOCKING_PUT_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  \
  `NONBLOCKING_GET_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  `NONBLOCKING_PEEK_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  \
endclass

// MACRO: `ovm_slave_imp_decl
//
// Define the class ovm_slave_impSFX for providing both blocking and
// non-blocking slave implementations.  ~SFX~ is the suffix for the new class
// type.

`define ovm_slave_imp_decl(SFX) \
class ovm_slave_imp``SFX #(type REQ=int, type RSP=int, type IMP=int, \
                           type REQ_IMP=IMP, type RSP_IMP=IMP) \
  extends ovm_port_base #(tlm_if_base #(RSP, REQ)); \
  typedef IMP     this_imp_type; \
  typedef REQ_IMP this_req_type; \
  typedef RSP_IMP this_rsp_type; \
  `OVM_MS_IMP_COMMON(`TLM_SLAVE_MASK,`"ovm_slave_imp``SFX`") \
  \
  `BLOCKING_PUT_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  `NONBLOCKING_PUT_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  \
  `BLOCKING_GET_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  `BLOCKING_PEEK_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  `NONBLOCKING_GET_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  `NONBLOCKING_PEEK_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  \
endclass

// MACRO: `ovm_blocking_transport_imp_decl
//
// Define the class ovm_blocking_transport_impSFX for providing the
// blocking transport implemenation.

`define ovm_blocking_transport_imp_decl(SFX) \
class ovm_blocking_transport_imp``SFX #(type REQ=int, type RSP=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(REQ, RSP)); \
  `OVM_IMP_COMMON(`TLM_BLOCKING_TRANSPORT_MASK,`"ovm_blocking_transport_imp``SFX`",IMP) \
  `BLOCKING_TRANSPORT_IMP_SFX(SFX, m_imp, REQ, RSP, req, rsp) \
endclass

// MACRO: `ovm_nonblocking_transport_imp_decl
//
// Define the class ovm_nonblocking_transport_impSFX for providing the
// non-blocking transport implemenation.

`define ovm_non_blocking_transport_imp_decl(SFX) \
  ovm_nonblocking_transport_imp_decl(SFX)

`define ovm_nonblocking_transport_imp_decl(SFX) \
class ovm_nonblocking_transport_imp``SFX #(type REQ=int, type RSP=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(REQ, RSP)); \
  `OVM_IMP_COMMON(`TLM_NONBLOCKING_TRANSPORT_MASK,`"ovm_nonblocking_transport_imp``SFX`",IMP) \
  `NONBLOCKING_TRANSPORT_IMP_SFX(SFX, m_imp, REQ, RSP, req, rsp) \
endclass

// MACRO: `ovm_transport_imp_decl
//
// Define the class ovm_transport_impSFX for providing both blocking and
// non-blocking transport implementations.  ~SFX~ is the suffix for the new class
// type.

`define ovm_transport_imp_decl(SFX) \
class ovm_transport_imp``SFX #(type REQ=int, type RSP=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(REQ, RSP)); \
  `OVM_IMP_COMMON(`TLM_TRANSPORT_MASK,`"ovm_transport_imp``SFX`",IMP) \
  `BLOCKING_TRANSPORT_IMP_SFX(SFX, m_imp, REQ, RSP, req, rsp) \
  `NONBLOCKING_TRANSPORT_IMP_SFX(SFX, m_imp, REQ, RSP, req, rsp) \
endclass

// MACRO: `ovm_analysis_imp_decl
//
// Define the class ovm_analysis_impSFX for providing an analysis
// implementation. ~SFX~ is the suffix for the new class type. The analysis 
// implemenation is the write function. The `ovm_analysis_imp_decl allows 
// for a scoreboard (or other analysis component) to support input from many 
// places. For example:
//
//| `ovm_analysis_imp_decl(_ingress)
//| `ovm_analysis_imp_port(_egress)
//|
//| class myscoreboard extends ovm_component;
//|   ovm_analysis_imp_ingress#(mydata, myscoreboard) ingress;
//|   ovm_analysis_imp_egress#(mydata, myscoreboard) egress;
//|   mydata ingress_list[$];
//|   ...
//|
//|   function new(string name, ovm_component parent);
//|     super.new(name,parent);
//|     ingress = new("ingress", this);
//|     egress = new("egress", this);
//|   endfunction
//|
//|   function void write_ingress(mydata t);
//|     ingress_list.push_back(t);
//|   endfunction
//|
//|   function void write_egress(mydata t);
//|     find_match_in_ingress_list(t);
//|   endfunction
//|
//|   function void find_match_in_ingress_list(mydata t);
//|     //implement scoreboarding for this particular dut
//|     ...
//|   endfunction
//| endclass

`define ovm_analysis_imp_decl(SFX) \
class ovm_analysis_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_ANALYSIS_MASK,`"ovm_analysis_imp``SFX`",IMP) \
  function void write( input T t); \
    m_imp.write``SFX( t); \
  endfunction \
  \
endclass


// These imps are used in ovm_*_port, ovm_*_export and ovm_*_imp, using suffixes
//

`define BLOCKING_PUT_IMP_SFX(SFX, imp, TYPE, arg) \
  task put( input TYPE arg); imp.put``SFX( arg); endtask

`define BLOCKING_GET_IMP_SFX(SFX, imp, TYPE, arg) \
  task get( output TYPE arg); imp.get``SFX( arg); endtask

`define BLOCKING_PEEK_IMP_SFX(SFX, imp, TYPE, arg) \
  task peek( output TYPE arg);imp.peek``SFX( arg); endtask

`define NONBLOCKING_PUT_IMP_SFX(SFX, imp, TYPE, arg) \
  function bit try_put( input TYPE arg); \
    if( !imp.try_put``SFX( arg)) return 0; \
    return 1; \
  endfunction \
  function bit can_put(); return imp.can_put``SFX(); endfunction

`define NONBLOCKING_GET_IMP_SFX(SFX, imp, TYPE, arg) \
  function bit try_get( output TYPE arg); \
    if( !imp.try_get``SFX( arg)) return 0; \
    return 1; \
  endfunction \
  function bit can_get(); return imp.can_get``SFX(); endfunction

`define NONBLOCKING_PEEK_IMP_SFX(SFX, imp, TYPE, arg) \
  function bit try_peek( output TYPE arg); \
    if( !imp.try_peek``SFX( arg)) return 0; \
    return 1; \
  endfunction \
  function bit can_peek(); return imp.can_peek``SFX(); endfunction

`define BLOCKING_TRANSPORT_IMP_SFX(SFX, imp, REQ, RSP, req_arg, rsp_arg) \
  task transport( input REQ req_arg, output RSP rsp_arg); \
    imp.transport``SFX(req_arg, rsp_arg); \
  endtask

`define NONBLOCKING_TRANSPORT_IMP_SFX(SFX, imp, REQ, RSP, req_arg, rsp_arg) \
  function bit nb_transport( input REQ req_arg, output RSP rsp_arg); \
    if(imp) return imp.nb_transport``SFX(req_arg, rsp_arg); \
  endfunction

//----------------------------------------------------------------------
// imp definitions
//----------------------------------------------------------------------
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

// primitive interfaces
`define TLM_BLOCKING_PUT_MASK          (1<<0)
`define TLM_BLOCKING_GET_MASK          (1<<1)
`define TLM_BLOCKING_PEEK_MASK         (1<<2)
`define TLM_BLOCKING_TRANSPORT_MASK    (1<<3)

`define TLM_NONBLOCKING_PUT_MASK       (1<<4)
`define TLM_NONBLOCKING_GET_MASK       (1<<5)
`define TLM_NONBLOCKING_PEEK_MASK      (1<<6)
`define TLM_NONBLOCKING_TRANSPORT_MASK (1<<7)

`define TLM_ANALYSIS_MASK              (1<<8)

`define TLM_MASTER_BIT_MASK            (1<<9)
`define TLM_SLAVE_BIT_MASK             (1<<10)
// combination interfaces
`define TLM_PUT_MASK                  (`TLM_BLOCKING_PUT_MASK    | `TLM_NONBLOCKING_PUT_MASK)
`define TLM_GET_MASK                  (`TLM_BLOCKING_GET_MASK    | `TLM_NONBLOCKING_GET_MASK)
`define TLM_PEEK_MASK                 (`TLM_BLOCKING_PEEK_MASK   | `TLM_NONBLOCKING_PEEK_MASK)

`define TLM_BLOCKING_GET_PEEK_MASK    (`TLM_BLOCKING_GET_MASK    | `TLM_BLOCKING_PEEK_MASK)
`define TLM_BLOCKING_MASTER_MASK      (`TLM_BLOCKING_PUT_MASK       | `TLM_BLOCKING_GET_MASK | `TLM_BLOCKING_PEEK_MASK | `TLM_MASTER_BIT_MASK)
`define TLM_BLOCKING_SLAVE_MASK       (`TLM_BLOCKING_PUT_MASK       | `TLM_BLOCKING_GET_MASK | `TLM_BLOCKING_PEEK_MASK | `TLM_SLAVE_BIT_MASK)

`define TLM_NONBLOCKING_GET_PEEK_MASK (`TLM_NONBLOCKING_GET_MASK | `TLM_NONBLOCKING_PEEK_MASK)
`define TLM_NONBLOCKING_MASTER_MASK   (`TLM_NONBLOCKING_PUT_MASK    | `TLM_NONBLOCKING_GET_MASK | `TLM_NONBLOCKING_PEEK_MASK | `TLM_MASTER_BIT_MASK)
`define TLM_NONBLOCKING_SLAVE_MASK    (`TLM_NONBLOCKING_PUT_MASK    | `TLM_NONBLOCKING_GET_MASK | `TLM_NONBLOCKING_PEEK_MASK | `TLM_SLAVE_BIT_MASK)

`define TLM_GET_PEEK_MASK             (`TLM_GET_MASK | `TLM_PEEK_MASK)
`define TLM_MASTER_MASK               (`TLM_BLOCKING_MASTER_MASK    | `TLM_NONBLOCKING_MASTER_MASK)
`define TLM_SLAVE_MASK                (`TLM_BLOCKING_SLAVE_MASK    | `TLM_NONBLOCKING_SLAVE_MASK)
`define TLM_TRANSPORT_MASK            (`TLM_BLOCKING_TRANSPORT_MASK | `TLM_NONBLOCKING_TRANSPORT_MASK)

`define SEQ_ITEM_GET_NEXT_ITEM_MASK       (1<<0)
`define SEQ_ITEM_TRY_NEXT_ITEM_MASK       (1<<1)
`define SEQ_ITEM_ITEM_DONE_MASK           (1<<2)
`define SEQ_ITEM_HAS_DO_AVAILABLE_MASK    (1<<3)
`define SEQ_ITEM_WAIT_FOR_SEQUENCES_MASK  (1<<4)
`define SEQ_ITEM_PUT_RESPONSE_MASK        (1<<5)
`define SEQ_ITEM_PUT_MASK                 (1<<6)
`define SEQ_ITEM_GET_MASK                 (1<<7)
`define SEQ_ITEM_PEEK_MASK                (1<<8)

`define SEQ_ITEM_PULL_MASK  (`SEQ_ITEM_GET_NEXT_ITEM_MASK | `SEQ_ITEM_TRY_NEXT_ITEM_MASK | \
                        `SEQ_ITEM_ITEM_DONE_MASK | `SEQ_ITEM_HAS_DO_AVAILABLE_MASK |  \
                        `SEQ_ITEM_WAIT_FOR_SEQUENCES_MASK | `SEQ_ITEM_PUT_RESPONSE_MASK | \
                        `SEQ_ITEM_PUT_MASK | `SEQ_ITEM_GET_MASK | `SEQ_ITEM_PEEK_MASK)

`define SEQ_ITEM_UNI_PULL_MASK (`SEQ_ITEM_GET_NEXT_ITEM_MASK | `SEQ_ITEM_TRY_NEXT_ITEM_MASK | \
                           `SEQ_ITEM_ITEM_DONE_MASK | `SEQ_ITEM_HAS_DO_AVAILABLE_MASK | \
                           `SEQ_ITEM_WAIT_FOR_SEQUENCES_MASK | `SEQ_ITEM_GET_MASK | \
                           `SEQ_ITEM_PEEK_MASK)

`define SEQ_ITEM_PUSH_MASK  (`SEQ_ITEM_PUT_MASK)

`include "tlm/tlm_imps.svh"
