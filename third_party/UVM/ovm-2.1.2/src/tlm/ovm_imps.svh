// $Id: //dvt/vtech/dev/main/ovm/src/tlm/ovm_imps.svh#14 $
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
//-------------.----------------------------------------------------------------

// Section: ovm_*_imp ports
//
// This page documents the following port classes
//
// - <ovm_*_imp #(T,IMP)> - unidirectional implementation ports
//
// - <ovm_*_imp #(REQ, RSP, IMP, REQ_IMP, RSP_IMP)> - bidirectional implementation ports
//

//------------------------------------------------------------------------------
//
// CLASS: ovm_*_imp #(T,IMP)
//
// Unidirectional implementation (imp) port classes--An imp port provides access
// to an implementation of the associated interface to all connected ~ports~ and
// ~exports~. Each imp port instance ~must~ be connected to the component instance
// that implements the associated interface, typically the imp port's parent.
// All other connections-- e.g. to other ports and exports-- are prohibited.
//
// The asterisk in ~ovm_*_imp~ may be any of the following
//
//|  blocking_put
//|  nonblocking_put
//|  put
//|
//|  blocking_get
//|  nonblocking_get
//|  get
//|
//|  blocking_peek
//|  nonblocking_peek
//|  peek
//|
//|  blocking_get_peek
//|  nonblocking_get_peek
//|  get_peek
//|
//|  analysis
//
// Type parameters
//
// T   - The type of transaction to be communicated by the imp
//
// IMP - The type of the component implementing the interface. That is, the class
//       to which this imp will delegate.
//
// The interface methods are implemented in a component of type ~IMP~, a handle
// to which is passed in a constructor argument.  The imp port delegates all
// interface calls to this component.
//
//------------------------------------------------------------------------------


// Function: new
// 
// Creates a new unidirectional imp port with the given ~name~ and ~parent~.
// The ~parent~ must implement the interface associated with this port.
// Its type must be the type specified in the imp's type-parameter, ~IMP~. 
//
//|  function new (string name, IMP parent);



class ovm_blocking_put_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_BLOCKING_PUT_MASK,"ovm_blocking_put_imp",IMP)
  `BLOCKING_PUT_IMP (m_imp, T, t)
endclass

class ovm_nonblocking_put_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_NONBLOCKING_PUT_MASK,"ovm_nonblocking_put_imp",IMP)
  `NONBLOCKING_PUT_IMP (m_imp, T, t)
endclass

class ovm_put_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_PUT_MASK,"ovm_put_imp",IMP)
  `PUT_IMP (m_imp, T, t)
endclass

class ovm_blocking_get_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_BLOCKING_GET_MASK,"ovm_blocking_get_imp",IMP)
  `BLOCKING_GET_IMP (m_imp, T, t)
endclass

class ovm_nonblocking_get_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_NONBLOCKING_GET_MASK,"ovm_nonblocking_get_imp",IMP)
  `NONBLOCKING_GET_IMP (m_imp, T, t)
endclass

class ovm_get_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_GET_MASK,"ovm_get_imp",IMP)
  `GET_IMP (m_imp, T, t)
endclass

class ovm_blocking_peek_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_BLOCKING_PEEK_MASK,"ovm_blocking_peek_imp",IMP)
  `BLOCKING_PEEK_IMP (m_imp, T, t)
endclass

class ovm_nonblocking_peek_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_NONBLOCKING_PEEK_MASK,"ovm_nonblocking_peek_imp",IMP)
  `NONBLOCKING_PEEK_IMP (m_imp, T, t)
endclass

class ovm_peek_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_PEEK_MASK,"ovm_peek_imp",IMP)
  `PEEK_IMP (m_imp, T, t)
endclass

class ovm_blocking_get_peek_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_BLOCKING_GET_PEEK_MASK,"ovm_blocking_get_peek_imp",IMP)
  `BLOCKING_GET_PEEK_IMP (m_imp, T, t)
endclass

class ovm_nonblocking_get_peek_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_NONBLOCKING_GET_PEEK_MASK,"ovm_nonblocking_get_peek_imp",IMP)
  `NONBLOCKING_GET_PEEK_IMP (m_imp, T, t)
endclass

class ovm_get_peek_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_GET_PEEK_MASK,"ovm_get_peek_imp",IMP)
  `GET_PEEK_IMP (m_imp, T, t)
endclass

class ovm_analysis_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_ANALYSIS_MASK,"ovm_analysis_imp",IMP)
  function void write (input T t);
    m_imp.write (t);
  endfunction
endclass


//------------------------------------------------------------------------------
//
// CLASS: ovm_*_imp #(REQ, RSP, IMP, REQ_IMP, RSP_IMP)
//
// Bidirectional implementation (imp) port classes--An imp port provides access
// to an implementation of the associated interface to all connected ~ports~ and
// ~exports~. Each imp port instance ~must~ be connected to the component instance
// that implements the associated interface, typically the imp port's parent.
// All other connections-- e.g. to other ports and exports-- are prohibited.
//
// The interface represented by the asterisk is any of the following
//
//|  blocking_transport
//|  nonblocking_transport
//|  transport
//|
//|  blocking_master
//|  nonblocking_master
//|  master
//|
//|  blocking_slave
//|  nonblocking_slave
//|  slave
//
// Type parameters
//
// REQ  - Request transaction type
//
// RSP  - Response transaction type 
//
// IMP  - Component type that implements the interface methods, typically the
//        the parent of this imp port.
//
// REQ_IMP - Component type that implements the request side of the
//           interface. Defaults to IMP. For master and slave imps only.
//
// RSP_IMP - Component type that implements the response side of the
//           interface. Defaults to IMP. For master and slave imps only.
//
// The interface methods are implemented in a component of type ~IMP~, a handle
// to which is passed in a constructor argument.  The imp port delegates all
// interface calls to this component.
//
// The master and slave imps have two modes of operation.
//
// - A single component of type IMP implements the entire interface for
//   both requests and responses. 
//
// - Two sibling components of type REQ_IMP and RSP_IMP implement the request
//   and response interfaces, respectively.  In this case, the IMP parent
//   instantiates this imp port ~and~ the REQ_IMP and RSP_IMP components.
//
// The second mode is needed when a component instantiates more than one imp
// port, as in the <tlm_req_rsp_channel #(REQ,RSP)> channel.
//
//------------------------------------------------------------------------------


// Function: new
//
// Creates a new bidirectional imp port with the given ~name~ and ~parent~.
// The ~parent~, whose type is specified by ~IMP~ type parameter,
// must implement the interface associated with this port.
//
// Transport imp constructor
//
//|  function new(string name, IMP imp)
//
// Master and slave imp constructor
//
// The optional ~req_imp~ and ~rsp_imp~ arguments, available to master and
// slave imp ports, allow the requests and responses to be handled by different
// subcomponents. If they are specified, they must point to the underlying
// component that implements the request and response methods, respectively. 
//
//|  function new(string name, IMP imp,
//|                            REQ_IMP req_imp=imp, RSP_IMP rsp_imp=imp)

class ovm_blocking_master_imp #(type REQ=int, type RSP=REQ, type IMP=int,
                                type REQ_IMP=IMP, type RSP_IMP=IMP)
  extends ovm_port_base #(tlm_if_base #(REQ, RSP));
  typedef IMP     this_imp_type;
  typedef REQ_IMP this_req_type;
  typedef RSP_IMP this_rsp_type;
  `OVM_MS_IMP_COMMON(`TLM_BLOCKING_MASTER_MASK,"ovm_blocking_master_imp")
  `BLOCKING_PUT_IMP (m_req_imp, REQ, t)
  `BLOCKING_GET_PEEK_IMP (m_rsp_imp, RSP, t)
endclass

class ovm_nonblocking_master_imp #(type REQ=int, type RSP=REQ, type IMP=int,
                                   type REQ_IMP=IMP, type RSP_IMP=IMP)
  extends ovm_port_base #(tlm_if_base #(REQ, RSP));
  typedef IMP     this_imp_type;
  typedef REQ_IMP this_req_type;
  typedef RSP_IMP this_rsp_type;
  `OVM_MS_IMP_COMMON(`TLM_NONBLOCKING_MASTER_MASK,"ovm_nonblocking_master_imp")
  `NONBLOCKING_PUT_IMP (m_req_imp, REQ, t)
  `NONBLOCKING_GET_PEEK_IMP (m_rsp_imp, RSP, t)
endclass

class ovm_master_imp #(type REQ=int, type RSP=REQ, type IMP=int,
                       type REQ_IMP=IMP, type RSP_IMP=IMP)
  extends ovm_port_base #(tlm_if_base #(REQ, RSP));
  typedef IMP     this_imp_type;
  typedef REQ_IMP this_req_type;
  typedef RSP_IMP this_rsp_type;
  `OVM_MS_IMP_COMMON(`TLM_MASTER_MASK,"ovm_master_imp")
  `PUT_IMP (m_req_imp, REQ, t)
  `GET_PEEK_IMP (m_rsp_imp, RSP, t)
endclass

class ovm_blocking_slave_imp #(type REQ=int, type RSP=REQ, type IMP=int,
                               type REQ_IMP=IMP, type RSP_IMP=IMP)
  extends ovm_port_base #(tlm_if_base #(RSP, REQ));
  typedef IMP     this_imp_type;
  typedef REQ_IMP this_req_type;
  typedef RSP_IMP this_rsp_type;
  `OVM_MS_IMP_COMMON(`TLM_BLOCKING_SLAVE_MASK,"ovm_blocking_slave_imp")
  `BLOCKING_PUT_IMP (m_rsp_imp, RSP, t)
  `BLOCKING_GET_PEEK_IMP (m_req_imp, REQ, t)
endclass

class ovm_nonblocking_slave_imp #(type REQ=int, type RSP=REQ, type IMP=int,
                                  type REQ_IMP=IMP, type RSP_IMP=IMP)
  extends ovm_port_base #(tlm_if_base #(RSP, REQ));
  typedef IMP     this_imp_type;
  typedef REQ_IMP this_req_type;
  typedef RSP_IMP this_rsp_type;
  `OVM_MS_IMP_COMMON(`TLM_NONBLOCKING_SLAVE_MASK,"ovm_nonblocking_slave_imp")
  `NONBLOCKING_PUT_IMP (m_rsp_imp, RSP, t)
  `NONBLOCKING_GET_PEEK_IMP (m_req_imp, REQ, t)
endclass

class ovm_slave_imp #(type REQ=int, type RSP=REQ, type IMP=int,
                      type REQ_IMP=IMP, type RSP_IMP=IMP)
  extends ovm_port_base #(tlm_if_base #(RSP, REQ));
  typedef IMP     this_imp_type;
  typedef REQ_IMP this_req_type;
  typedef RSP_IMP this_rsp_type;
  `OVM_MS_IMP_COMMON(`TLM_SLAVE_MASK,"ovm_slave_imp")
  `PUT_IMP (m_rsp_imp, RSP, t)
  `GET_PEEK_IMP (m_req_imp, REQ, t)
endclass

class ovm_blocking_transport_imp #(type REQ=int, type RSP=REQ, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(REQ, RSP));
  `OVM_IMP_COMMON(`TLM_BLOCKING_TRANSPORT_MASK,"ovm_blocking_transport_imp",IMP)
  `BLOCKING_TRANSPORT_IMP (m_imp, REQ, RSP, req, rsp)
endclass

class ovm_nonblocking_transport_imp #(type REQ=int, type RSP=REQ, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(REQ, RSP));
  `OVM_IMP_COMMON(`TLM_NONBLOCKING_TRANSPORT_MASK,"ovm_nonblocking_transport_imp",IMP)
  `NONBLOCKING_TRANSPORT_IMP (m_imp, REQ, RSP, req, rsp)
endclass

class ovm_transport_imp #(type REQ=int, type RSP=REQ, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(REQ, RSP));
  `OVM_IMP_COMMON(`TLM_TRANSPORT_MASK,"ovm_transport_imp",IMP)
  `BLOCKING_TRANSPORT_IMP (m_imp, REQ, RSP, req, rsp)
  `NONBLOCKING_TRANSPORT_IMP (m_imp, REQ, RSP, req, rsp)
endclass

