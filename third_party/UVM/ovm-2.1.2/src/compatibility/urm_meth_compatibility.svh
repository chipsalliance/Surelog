// $Id: urm_meth_compatibility.svh,v 1.5 2008/10/09 14:46:21 jlrose Exp $
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
`ifndef URM_METH_COMPATIBILITY_SVH
`define URM_METH_COMPATIBILITY_SVH


//typedef ovm_sequence_base      urm_item;
typedef ovm_sequence_item      urm_sequence_item;
//typedef ovm_sequence           urm_sequence;
typedef ovm_sequence_base      urm_sequence;
//typedef ovm_random_sequence    urm_random_sequence;
//typedef ovm_simple_sequence    urm_simple_sequence;
//typedef ovm_main_sequence      urm_main_sequence;
//typedef ovm_sequencer          urm_driver;
typedef ovm_sequencer_base          urm_driver;
//typedef ovm_virtual_sequencer  urm_virtual_driver;
typedef ovm_sequencer_base  urm_virtual_driver;
//typedef ovm_driver             urm_bfm;
typedef ovm_agent              urm_agent;
typedef ovm_monitor            urm_monitor;
typedef ovm_test               urm_test;
typedef ovm_env                urm_env;

//
// TLM Adapters to allow backward compatibility
// --------------------------------------------

typedef enum {
  URM_ZERO_OR_MORE_BOUND,
  URM_ONE_OR_MORE_BOUND,
  URM_ALL_BOUND = 255
} urm_port_policy;

`define tlm_port_compat_new_func \
  function new( string name , ovm_component parent , \
                urm_port_policy policy=URM_ONE_OR_MORE_BOUND ); \
    super.new(name,parent,0,policy); \
  endfunction

`define tlm_export_compat_new_func(T) \
  function new( string name , T imp , \
                urm_port_policy policy=URM_ONE_OR_MORE_BOUND ); \
    super.new(name,imp); \
  endfunction

class tlm_b_put_port#(type T=int) extends ovm_blocking_put_port#(T);
  `tlm_port_compat_new_func
endclass

class tlm_nb_put_port#(type T=int) extends ovm_nonblocking_put_port#(T);
  `tlm_port_compat_new_func
endclass

class tlm_put_port#(type T=int) extends ovm_put_port#(T);
  `tlm_port_compat_new_func
endclass

class tlm_b_put_export#(type T1=int, type T2=int) extends ovm_blocking_put_imp#(T1,T2);
  `tlm_export_compat_new_func(T2)
endclass

class tlm_nb_put_export#(type T1=int, type T2=int) extends ovm_nonblocking_put_imp#(T1,T2);
  `tlm_export_compat_new_func(T2)
endclass

class tlm_put_export#(type T1=int, type T2=int) extends ovm_put_imp#(T1,T2);
  `tlm_export_compat_new_func(T2)
endclass

class tlm_b_get_port#(type T=int) extends ovm_blocking_get_port#(T);
  `tlm_port_compat_new_func
endclass

class tlm_nb_get_port#(type T=int) extends ovm_nonblocking_get_port#(T);
  `tlm_port_compat_new_func
endclass

class tlm_get_port#(type T=int) extends ovm_get_port#(T);
  `tlm_port_compat_new_func
endclass

class tlm_b_get_export#(type T1=int, type T2=int) extends ovm_blocking_get_imp#(T1,T2);
  `tlm_export_compat_new_func(T2)
endclass

class tlm_nb_get_export#(type T1=int, type T2=int) extends ovm_nonblocking_get_imp#(T1,T2);
  `tlm_export_compat_new_func(T2)
endclass

class tlm_get_export#(type T1=int, type T2=int) extends ovm_get_imp#(T1,T2);
  `tlm_export_compat_new_func(T2)
endclass

class urm_fifo#(type T=ovm_object) extends tlm_fifo#(T);
  function new (string name, ovm_component parent, int size=1);
    super.new(name, parent, size);
  endfunction
endclass

`endif
