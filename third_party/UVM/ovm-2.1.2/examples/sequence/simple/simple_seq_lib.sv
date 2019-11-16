// $Id: simple_seq_lib.sv,v 1.8 2009/10/30 15:29:21 jlrose Exp $
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

`ifndef SIMPLE_SEQ_LIB_SV
`define SIMPLE_SEQ_LIB_SV

//------------------------------------------------------------------------------
//
// SEQUENCE: simple_seq_do
//
//------------------------------------------------------------------------------

class simple_seq_do extends ovm_sequence #(simple_item);

  function new(string name="simple_seq_do");
    super.new(name);
  endfunction
  
  `ovm_sequence_utils(simple_seq_do, simple_sequencer)    

  virtual task body();
    `ovm_info(get_name(), $psprintf("In body() of %s", get_name()),1000)
    `ovm_do(req)
  endtask
  
endclass : simple_seq_do


//------------------------------------------------------------------------------
//
// SEQUENCE: simple_seq_do_with
//
//------------------------------------------------------------------------------

class simple_seq_do_with extends ovm_sequence #(simple_item);

  function new(string name="simple_seq_do_with");
    super.new(name);
  endfunction
  
  `ovm_sequence_utils(simple_seq_do_with, simple_sequencer)

  virtual task body();
    `ovm_info(get_name(), $psprintf("In body() of %s", get_name()),1000)
    `ovm_do_with(req, { req.addr == 16'h0123; req.data == 16'h0456; } )
  endtask
  
endclass : simple_seq_do_with


//------------------------------------------------------------------------------
//
// SEQUENCE: simple_seq_do_with_vars
//
//------------------------------------------------------------------------------

class simple_seq_do_with_vars extends ovm_sequence #(simple_item);

  function new(string name="simple_seq_do_with_vars");
    super.new(name);
  endfunction
  
  `ovm_sequence_utils(simple_seq_do_with_vars, simple_sequencer)    

  rand int unsigned start_addr;
    constraint c1 { start_addr < 16'h0200; }
  rand int unsigned start_data;
    constraint c2 { start_data < 16'h0100; }

  virtual task body();
    `ovm_info(get_name(), $psprintf("In body() of %s", get_name()),1000)
    `ovm_do_with(req, { req.addr == start_addr; req.data == start_data; } )
  endtask
  
endclass : simple_seq_do_with_vars


//------------------------------------------------------------------------------
//
// SEQUENCE: simple_seq_sub_seqs
//
//------------------------------------------------------------------------------

class simple_seq_sub_seqs extends ovm_sequence #(simple_item);

  function new(string name="simple_seq_sub_seqs");
    super.new(name);
  endfunction
  
  `ovm_sequence_utils(simple_seq_sub_seqs, simple_sequencer)    

  simple_seq_do seq_do;
  simple_seq_do_with seq_do_with;
  simple_seq_do_with_vars seq_do_with_vars;

  virtual task body();
    `ovm_info(get_name(), $psprintf("In body() of %s", get_name()),1000)
    #100;
    `ovm_do(seq_do)
    #100;
    `ovm_do(seq_do_with)
    #100;
    `ovm_do_with(seq_do_with_vars, { seq_do_with_vars.start_addr == 16'h0003; seq_do_with_vars.start_data == 16'h0009; } )
  endtask
  
endclass : simple_seq_sub_seqs


`endif // SIMPLE_SEQ_LIB_SV

