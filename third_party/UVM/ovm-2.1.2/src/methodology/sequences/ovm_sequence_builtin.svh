// $Id: ovm_sequence_builtin.svh,v 1.18 2009/12/14 22:39:41 jlrose Exp $
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

`ifndef OVM_SEQUENCE_BUILTIN_SVH
`define OVM_SEQUENCE_BUILTIN_SVH

`include "methodology/ovm_meth_defines.svh"


//------------------------------------------------------------------------------
//
// CLASS: ovm_random_sequence
//
// This sequence randomly selects and executes a sequence from the sequencer¿s
// sequence library, excluding ovm_random_sequence itself, and
// ovm_exhaustive_sequence. 
//
// The ovm_random_sequence class is a built-in sequence that is preloaded into
// every sequencer's sequence library with the name "ovm_random_sequence".
//
// The number of selections and executions is determined by the count property
// of the sequencer (or virtual sequencer) on which ovm_random_sequence is
// operating. See <ovm_sequencer_base> for more information.
//
//------------------------------------------------------------------------------

class ovm_random_sequence extends ovm_sequence #(ovm_sequence_item);

  rand protected int unsigned l_count=-1;
  local int unsigned l_exhaustive_seq_kind;
  local int unsigned max_kind;
  rand local int unsigned l_kind;
  protected bit m_success;

// Function: get_count
//
// Returns the count of the number of sub-sequences which are randomly generated.
// By default, count is equal to the value from the sequencer's count variable.
// However, if the sequencer's count variable is -1, then a random value between
// 0 and sequencer.max_random_count (exclusive) is chosen. The sequencer's
// count variable is subsequently reset to the random value that was used. If
// get_count() is call before the sequence has started, the return value will
// be sequencer.count, which may be -1.

function int unsigned get_count();
  if(l_count == -1) return m_sequencer.count;
  return l_count;
endfunction

// new
// ---

function new(string name="ovm_random_sequence");
  super.new(name);
endfunction


// body
// ----

task body();
  pick_sequence.constraint_mode(0);
  if (m_sequencer.count == -1) begin
    if (!randomize(l_count) with { l_count > 0 && l_count <
      m_sequencer.max_random_count; })
      ovm_report_fatal("RANDSEQ", "Randomization for l_count failed in random sequence body", OVM_NONE);
    m_sequencer.count = l_count;
  end
  else
    l_count = m_sequencer.count;
  max_kind = m_sequencer.sequences.size();
  l_exhaustive_seq_kind = m_sequencer.get_seq_kind("ovm_exhaustive_sequence");
  repeat (l_count) begin
    if (!randomize(l_kind) with { l_kind > l_exhaustive_seq_kind && 
      l_kind < max_kind; })
      ovm_report_fatal("RANDSEQ", "Randomization for l_kind failed in random sequence body", OVM_NONE);
    do_sequence_kind(l_kind);
  end
  m_sequencer.m_random_count++;
  pick_sequence.constraint_mode(1);
endtask 


//Implement data functions
function void do_copy (ovm_object rhs);
  ovm_random_sequence seq;
  if(rhs==null) return;
  if(!$cast(seq, rhs)) return;
  l_count = seq.l_count;
endfunction

function bit do_compare (ovm_object rhs, ovm_comparer comparer);
  ovm_random_sequence seq;
  do_compare = 1;
  if(rhs==null) return 0;
  if(!$cast(seq, rhs)) return 0;
  do_compare &= comparer.compare_field_int("l_count", l_count, seq.l_count, 
    $bits(l_count));
endfunction

function void do_print (ovm_printer printer);
  printer.print_field("l_count", l_count, $bits(l_count));
endfunction

function void do_record (ovm_recorder recorder);
  recorder.record_field("l_count", l_count, $bits(l_count));
endfunction // void

  function ovm_object create (string name="");
    ovm_random_sequence i; i=new(name);
    return i;
  endfunction

  virtual function string get_type_name();
     return "ovm_random_sequence";
  endfunction

  // Macro for factory creation
  `ovm_object_registry(ovm_random_sequence, "ovm_random_sequence")

endclass


//------------------------------------------------------------------------------
//
// CLASS: ovm_exhaustive_sequence
//
// This sequence randomly selects and executes each sequence from the
// sequencer's sequence library once, excluding itself and ovm_random_sequence.
//
// The ovm_exhaustive_sequence class is a built-in sequence that is preloaded 
// into every sequencer's sequence library with the name
// "ovm_exaustive_sequence".
//
//------------------------------------------------------------------------------

class ovm_exhaustive_sequence extends ovm_sequence #(ovm_sequence_item);

  rand protected int unsigned l_count;
  local int unsigned l_exhaustive_seq_kind;
  local int unsigned max_kind;
  randc local bit[9:0] l_kind;
  protected bit m_success;

// new
// ---

function new(string name="ovm_exhaustive_sequence");
  super.new(name);
endfunction


// body
// ----

task body();
    int i;
    
  pick_sequence.constraint_mode(0);


    //for (i = 0; i < m_sequencer.num_sequences(); i++ ) begin
    //  $display("seq: %0d: %s", i, m_sequencer.sequences[i]);
    //  $display("get_seq_kind[%s]: %0d", m_sequencer.sequences[i], get_seq_kind(m_sequencer.sequences[i]));
    //end
    
    
  l_count = m_sequencer.sequences.size() - 2;
  max_kind = m_sequencer.sequences.size();
  l_exhaustive_seq_kind = m_sequencer.get_seq_kind("ovm_exhaustive_sequence");
  repeat (l_count) begin
    if (!randomize(l_kind) with { l_kind > l_exhaustive_seq_kind; 
      l_kind < max_kind; }) // l_kind is randc
      ovm_report_fatal("RANDSEQ", "Randomization for l_kind failed in exhaustive sequence body", OVM_NONE);

    do_sequence_kind(l_kind);
  end
  m_sequencer.m_exhaustive_count++;
  pick_sequence.constraint_mode(1);
endtask 


//Implement data functions
function void do_copy (ovm_object rhs);
  ovm_exhaustive_sequence seq;
  if(rhs==null) return;
  if(!$cast(seq, rhs)) return;
  l_count = seq.l_count;
endfunction

function bit do_compare (ovm_object rhs, ovm_comparer comparer);
  ovm_exhaustive_sequence seq;
  do_compare = 1;
  if(rhs==null) return 0;
  if(!$cast(seq, rhs)) return 0;
  do_compare &= comparer.compare_field_int("l_count", l_count, seq.l_count, 
    $bits(l_count));
endfunction

function void do_print (ovm_printer printer);
  printer.print_field("l_count", l_count, $bits(l_count));
endfunction

function void do_record (ovm_recorder recorder);
  recorder.record_field("l_count", l_count, $bits(l_count));
endfunction // void

function ovm_object create (string name="");
  ovm_exhaustive_sequence i; i=new(name);
  return i;
endfunction

virtual function string get_type_name();
   return "ovm_exhaustive_sequence";
endfunction

// Macro for factory creation
`ovm_object_registry(ovm_exhaustive_sequence, "ovm_exhaustive_sequence")

endclass


//------------------------------------------------------------------------------
//
// CLASS: ovm_simple_sequence
//
// This sequence simply executes a single sequence item. 
//
// The item parameterization of the sequencer on which the ovm_simple_sequence
// is executed defines the actual type of the item executed.
//
// The ovm_simple_sequence class is a built-in sequence that is preloaded into
// every sequencer's sequence library with the name "ovm_simple_sequence". 
//
// See <ovm_sequencer #(REQ,RSP)> for more information on running sequences.
//
//------------------------------------------------------------------------------

class ovm_simple_sequence extends ovm_sequence #(ovm_sequence_item);

  protected rand ovm_sequence_item item;

  // new
  // ---
  function new (string name="ovm_simple_sequence");
    super.new(name);
  endfunction

  // body
  // ----
  task body();
    `ovm_do(item)
    m_sequencer.m_simple_count++;
  endtask

  function ovm_object create (string name="");
    ovm_simple_sequence i;
    i=new(name);
    return i;
  endfunction

  virtual function string get_type_name();
     return "ovm_simple_sequence";
  endfunction

  // Macro for factory creation
  `ovm_object_registry(ovm_simple_sequence, "ovm_simple_sequence")

endclass

// Section: end
`endif // OVM_SEQUENCE_BUILTIN_SVH
