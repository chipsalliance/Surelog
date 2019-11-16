// $Id: simple_seq_lib.sv,v 1.3 2007/12/14 10:18:56 redelman Exp $
//----------------------------------------------------------------------
//   Copyright 2007-2008 Mentor Graphics Corporation
//   Copyright 2007-2008 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Ported to VMM, 2008 by Synopsys, Inc.
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

class simple_seq_do extends simple_item_scenario;

  int SEQ = define_scenario("simple_seq_do", 1);

  constraint simple_seq_do_with_valid {
     length == 1;
  }

  virtual task apply(simple_item_channel channel,
                     ref int unsigned    n_insts);
    `vmm_note(channel.log, "Applying simple_seq_do...");
    super.apply(channel, n_insts);
  endtask
endclass : simple_seq_do


//------------------------------------------------------------------------------
//
// SEQUENCE: simple_seq_do_with
//
//------------------------------------------------------------------------------

class simple_seq_do_with extends simple_item_scenario;

  int SEQ = define_scenario("simple_seq_do_with", 1);

  constraint simple_seq_do_with_valid {
     length == 1;
     items[0].addr == 16'h0123;
     items[0].data == 16'h0456;
  }

  virtual task apply(simple_item_channel channel,
                     ref int unsigned    n_insts);
    `vmm_note(channel.log, "Applying simple_seq_do_with...");
    super.apply(channel, n_insts);
  endtask
endclass : simple_seq_do_with


//------------------------------------------------------------------------------
//
// SEQUENCE: simple_seq_do_with_vars
//
//------------------------------------------------------------------------------

class simple_seq_do_with_vars extends simple_item_scenario;

  int SEQ = define_scenario("simple_seq_do_with_vars", 1);

  rand int unsigned start_addr;
    constraint c1 { start_addr < 16'h0200; }
  rand int unsigned start_data;
    constraint c2 { start_data < 16'h0100; }
  simple_item item;

  constraint simple_seq_do_with_valid {
     length == 1;
     items[0].addr == start_addr;
     items[0].data == start_data;
  }

  virtual task apply(simple_item_channel channel,
                     ref int unsigned    n_insts);
    `vmm_note(channel.log, "Applying simple_seq_do_with_vars...");
    super.apply(channel, n_insts);
  endtask
  
endclass : simple_seq_do_with_vars


//------------------------------------------------------------------------------
//
// SEQUENCE: simple_seq_sub_seqs
//
//------------------------------------------------------------------------------

class simple_seq_sub_seqs extends simple_item_scenario;

  int SEQ = define_scenario("simple_seq_sub_seqs", 0);

  rand simple_seq_do seq_do;
  rand simple_seq_do_with seq_do_with;
  rand simple_seq_do_with_vars seq_do_with_vars;

  constraint simple_seq_sub_seqs_valid {
     seq_do_with_vars.start_addr == 16'h0003;
     seq_do_with_vars.start_data == 16'h0009;
  }


  function new();
     this.seq_do = new;
     this.seq_do_with = new;
     this.seq_do_with_vars = new;
  endfunction

  virtual task apply(simple_item_channel channel,
                     ref int unsigned    n_insts);
    `vmm_note(channel.log, "Applying simple_seq_sub_seqs...");
    #100;
    this.seq_do.apply(channel, n_insts);
    #100;
    this.seq_do_with.apply(channel, n_insts);
    #100;
    this.seq_do_with_vars.apply(channel, n_insts);
  endtask
  
endclass : simple_seq_sub_seqs

`endif // SIMPLE_SEQ_LIB_SV
