// $Id: //dvt/vtech/dev/main/ovm/src/tlm/ovm_ports.svh#16 $
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

//------------------------------------------------------------------------------
//
// CLASS: ovm_*_port #(T)
//
// These unidirectional ports are instantiated by components that ~require~,
// or ~use~, the associated interface to convey transactions. A port can
// be connected to any compatible port, export, or imp port. Unless its
// ~min_size~ is 0, a port ~must~ be connected to at least one implementation
// of its assocated interface.
//
// The asterisk in ~ovm_*_port~ is any of the following
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
// T - The type of transaction to be communicated by the export
//
// Ports are connected to interface implementations directly via 
// <ovm_*_imp #(T,IMP)> ports or indirectly via hierarchical connections
// to <ovm_*_port #(T)> and <ovm_*_export #(T)> ports.
//
//------------------------------------------------------------------------------


// Function: new
// 
// The ~name~ and ~parent~ are the standard <ovm_component> constructor arguments.
// The ~min_size~ and ~max_size~ specify the minimum and maximum number of
// interfaces that must have been connected to this port by the end of elaboration.
//
//|  function new (string name, 
//|                ovm_component parent,
//|                int min_size=1,
//|                int max_size=1)


class ovm_blocking_put_port #(type T=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_PORT_COMMON(`TLM_BLOCKING_PUT_MASK,"ovm_blocking_put_port")
  `BLOCKING_PUT_IMP (this.m_if, T, t)
endclass 

class ovm_nonblocking_put_port #(type T=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_PORT_COMMON(`TLM_NONBLOCKING_PUT_MASK,"ovm_nonblocking_put_port")
  `NONBLOCKING_PUT_IMP (this.m_if, T, t)
endclass

class ovm_put_port #(type T=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_PORT_COMMON(`TLM_PUT_MASK,"ovm_put_port")
  `PUT_IMP (this.m_if, T, t)
endclass

class ovm_blocking_get_port #(type T=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_PORT_COMMON(`TLM_BLOCKING_GET_MASK,"ovm_blocking_get_port")
  `BLOCKING_GET_IMP (this.m_if, T, t)
endclass 

class ovm_nonblocking_get_port #(type T=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_PORT_COMMON(`TLM_NONBLOCKING_GET_MASK,"ovm_nonblocking_get_port")
  `NONBLOCKING_GET_IMP (this.m_if, T, t)
endclass

class ovm_get_port #(type T=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_PORT_COMMON(`TLM_GET_MASK,"ovm_get_port")
  `GET_IMP (this.m_if, T, t)
endclass 

class ovm_blocking_peek_port #(type T=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_PORT_COMMON(`TLM_BLOCKING_PEEK_MASK,"ovm_blocking_peek_port")
  `BLOCKING_PEEK_IMP (this.m_if, T, t)
endclass 

class ovm_nonblocking_peek_port #(type T=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_PORT_COMMON(`TLM_NONBLOCKING_PEEK_MASK,"ovm_nonblocking_peek_port")
  `NONBLOCKING_PEEK_IMP (this.m_if, T, t)
endclass

class ovm_peek_port #(type T=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_PORT_COMMON(`TLM_PEEK_MASK,"ovm_peek_port")
  `PEEK_IMP (this.m_if, T, t)
endclass 

class ovm_blocking_get_peek_port #(type T=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_PORT_COMMON(`TLM_BLOCKING_GET_PEEK_MASK,"ovm_blocking_get_peek_port")
  `BLOCKING_GET_PEEK_IMP (this.m_if, T, t)
endclass 

class ovm_nonblocking_get_peek_port #(type T=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_PORT_COMMON(`TLM_NONBLOCKING_GET_PEEK_MASK,"ovm_nonblocking_get_peek_port")
  `NONBLOCKING_GET_PEEK_IMP (this.m_if, T, t)
endclass

class ovm_get_peek_port #(type T=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_PORT_COMMON(`TLM_GET_PEEK_MASK,"ovm_get_peek_port")
  `GET_PEEK_IMP (this.m_if, T, t)
endclass 

class ovm_analysis_port # (type T = int)
  extends ovm_port_base # (tlm_if_base #(T,T));

  function new (string name, ovm_component parent);
    super.new (name, parent, OVM_PORT, 0, OVM_UNBOUNDED_CONNECTIONS);
    m_if_mask = `TLM_ANALYSIS_MASK;  
  endfunction

  virtual function string get_type_name();
    return "ovm_analysis_port";
  endfunction

  // analysis port differs from other ports in that it broadcasts
  // to all connected interfaces. Ports only send to the interface
  // at the index specified in a call to set_if (0 by default).
  function void write (input T t);
    tlm_if_base # (T, T) tif;
    for (int i = 0; i < this.size(); i++) begin
      tif = this.get_if (i);
      if ( tif == null )
        ovm_report_fatal ("NTCONN", {"No tlm interface is connected to ", get_full_name(), " for executing write()"}, OVM_NONE);
      tif.write (t);
    end 
  endfunction

endclass


//------------------------------------------------------------------------------
//
// CLASS: ovm_*_port #(REQ,RSP)
//
// These bidirectional ports are instantiated by components that ~require~,
// or ~use~, the associated interface to convey transactions. A port can
// be connected to any compatible port, export, or imp port. Unless its
// ~min_size~ is 0, a port ~must~ be connected to at least one implementation
// of its assocated interface.
//
// The asterisk in ~ovm_*_port~ is any of the following
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
// Ports are connected to interface implementations directly via 
// <ovm_*_imp #(REQ,RSP,IMP,REQ_IMP,RSP_IMP)> ports or indirectly via
// hierarchical connections to <ovm_*_port #(REQ,RSP)> and
// <ovm_*_export #(REQ,RSP)> ports.
//
// Type parameters
//
// REQ - The type of request transaction to be communicated by the export
//
// RSP - The type of response transaction to be communicated by the export
//
//------------------------------------------------------------------------------

// Function: new
// 
// The ~name~ and ~parent~ are the standard <ovm_component> constructor arguments.
// The ~min_size~ and ~max_size~ specify the minimum and maximum number of
// interfaces that must have been supplied to this port by the end of elaboration.
//
//   function new (string name, 
//                 ovm_component parent,
//                 int min_size=1,
//                 int max_size=1)


class ovm_blocking_master_port #(type REQ=int, type RSP=REQ)
  extends ovm_port_base #(tlm_if_base #(REQ, RSP));
  `OVM_PORT_COMMON(`TLM_BLOCKING_MASTER_MASK,"ovm_blocking_master_port")
  `BLOCKING_PUT_IMP (this.m_if, REQ, t)
  `BLOCKING_GET_PEEK_IMP (this.m_if, RSP, t)
endclass 

class ovm_nonblocking_master_port #(type REQ=int, type RSP=REQ)
  extends ovm_port_base #(tlm_if_base #(REQ, RSP));
  `OVM_PORT_COMMON(`TLM_NONBLOCKING_MASTER_MASK,"ovm_nonblocking_master_port")
  `NONBLOCKING_PUT_IMP (this.m_if, REQ, t)
  `NONBLOCKING_GET_PEEK_IMP (this.m_if, RSP, t)
endclass 

class ovm_master_port #(type REQ=int, type RSP=REQ)
  extends ovm_port_base #(tlm_if_base #(REQ, RSP));
  `OVM_PORT_COMMON(`TLM_MASTER_MASK,"ovm_master_port")
  `PUT_IMP (this.m_if, REQ, t)
  `GET_PEEK_IMP (this.m_if, RSP, t)
endclass

class ovm_blocking_slave_port #(type REQ=int, type RSP=REQ)
  extends ovm_port_base #(tlm_if_base #(RSP, REQ));
  `OVM_PORT_COMMON(`TLM_BLOCKING_SLAVE_MASK,"ovm_blocking_slave_port")
  `BLOCKING_PUT_IMP (this.m_if, RSP, t)
  `BLOCKING_GET_PEEK_IMP (this.m_if, REQ, t)
endclass 

class ovm_nonblocking_slave_port #(type REQ=int, type RSP=REQ)
  extends ovm_port_base #(tlm_if_base #(RSP, REQ));
  `OVM_PORT_COMMON(`TLM_NONBLOCKING_SLAVE_MASK,"ovm_nonblocking_slave_port")
  `NONBLOCKING_PUT_IMP (this.m_if, RSP, t)
  `NONBLOCKING_GET_PEEK_IMP (this.m_if, REQ, t)
endclass 

class ovm_slave_port #(type REQ=int, type RSP=REQ)
  extends ovm_port_base #(tlm_if_base #(RSP, REQ));
  `OVM_PORT_COMMON(`TLM_SLAVE_MASK,"ovm_slave_port")
  `PUT_IMP (this.m_if, RSP, t)
  `GET_PEEK_IMP (this.m_if, REQ, t)
endclass

class ovm_blocking_transport_port #(type REQ=int, type RSP=REQ)
  extends ovm_port_base #(tlm_if_base #(REQ, RSP));
  `OVM_PORT_COMMON(`TLM_BLOCKING_TRANSPORT_MASK,"ovm_blocking_transport_port")
  `BLOCKING_TRANSPORT_IMP (this.m_if, REQ, RSP, req, rsp)
endclass

class ovm_nonblocking_transport_port #(type REQ=int, type RSP=REQ)
  extends ovm_port_base #(tlm_if_base #(REQ, RSP));
  `OVM_PORT_COMMON(`TLM_NONBLOCKING_TRANSPORT_MASK,"ovm_nonblocking_transport_port")
  `NONBLOCKING_TRANSPORT_IMP (this.m_if, REQ, RSP, req, rsp)
endclass

class ovm_transport_port #(type REQ=int, type RSP=REQ)
  extends ovm_port_base #(tlm_if_base #(REQ, RSP));
  `OVM_PORT_COMMON(`TLM_TRANSPORT_MASK,"ovm_transport_port")
  `TRANSPORT_IMP (this.m_if, REQ, RSP, req, rsp)
endclass

