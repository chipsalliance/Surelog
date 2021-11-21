//------------------------------------------------------------------------------
//  Copyright 2020 Taichi Ishitani
//
//  Licensed under the Apache License, Version 2.0 (the "License");
//  you may not use this file except in compliance with the License.
//  You may obtain a copy of the License at
//
//  http://www.apache.org/licenses/LICENSE-2.0
//
//  Unless required by applicable law or agreed to in writing, software
//  distributed under the License is distributed on an "AS IS" BASIS,
//  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//  See the License for the specific language governing permissions and
//  limitations under the License.
//------------------------------------------------------------------------------
`ifndef TUE_SEQUENCE_DEFINES_SVH
`define TUE_SEQUENCE_DEFINES_SVH

`define tue_create_on(SEQ_OR_ITEM, SEQR) \
begin \
  uvm_object_wrapper  __wrapper; \
  __wrapper = SEQ_OR_ITEM.get_type(); \
  $cast(SEQ_OR_ITEM, this.create_item(__wrapper, SEQR, `"SEQ_OR_ITEM`")); \
end

`define tue_create(SEQ_OR_ITEM) \
`tue_create_on(SEQ_OR_ITEM, m_sequencer)

`define tue_do_on_with(SEQ_OR_ITEM, SEQR, CONSTRAINTS) \
begin \
  uvm_sequence_base __seq; \
  `tue_create_on(SEQ_OR_ITEM, SEQR) \
  void'($cast(__seq, SEQ_OR_ITEM)); \
  if (__seq == null) begin \
    this.start_item(SEQ_OR_ITEM, -1); \
  end \
  if ((__seq == null) || (!__seq.do_not_randomize)) begin \
    if (!SEQ_OR_ITEM.randomize() with CONSTRAINTS) begin \
      `uvm_fatal("RNDFLD", "Randomization failed in tue_do_with action") \
    end \
  end \
  if (__seq == null) begin \
    this.finish_item(SEQ_OR_ITEM, -1); \
  end \
  else begin \
    __seq.start(SEQR, this, -1, 0); \
  end \
end

`define tue_do_on(SEQ_OR_ITEM, SEQR) \
`tue_do_on_with(SEQ_OR_ITEM, SEQR, {})

`define tue_do_with(SEQ_OR_ITEM, CONSTRAINTS) \
`tue_do_on_with(SEQ_OR_ITEM, m_sequencer, CONSTRAINTS)

`define tue_do(SEQ_OR_ITEM) \
`tue_do_on_with(SEQ_OR_ITEM, m_sequencer, {})

`define tue_fork_do_on_with(SEQ_OR_ITEM, SEQR, CONSTRAINTS) \
begin \
  uvm_sequence_base __seq; \
  uvm_sequence_item __item; \
  `tue_create_on(SEQ_OR_ITEM, SEQR) \
  void'($cast(__seq, SEQ_OR_ITEM)); \
  void'($cast(__item, SEQ_OR_ITEM)); \
  if (__seq == null) begin \
    start_item(SEQ_OR_ITEM, -1); \
  end \
  if ((__seq == null) || (!__seq.do_not_randomize)) begin \
    if (!SEQ_OR_ITEM.randomize() with CONSTRAINTS) begin \
      `uvm_fatal("RNDFLD", "Randomization failed in tue_do_with action") \
    end \
  end \
  fork \
    automatic uvm_sequence_base __seq_temp  = __seq; \
    automatic uvm_sequence_item __item_temp = __item; \
    begin \
      if (__seq_temp != null) begin \
        __seq_temp.start(__seq_temp.get_sequencer(), this, -1, 0); \
      end \
      else begin \
        finish_item(__item_temp, -1); \
      end \
    end \
  join_none \
  #0; \
end

`define tue_fork_do_on(SEQ_OR_ITEM, SEQR) \
`tue_fork_do_on_with(SEQ_OR_ITEM, SEQR, {})

`define tue_fork_do_with(SEQ_OR_ITEM, CONSTRAINTS) \
`tue_fork_do_on_with(SEQ_OR_ITEM, m_sequencer, CONSTRAINTS)

`define tue_fork_do(SEQ_OR_ITEM) \
`tue_fork_do_on_with(SEQ_OR_ITEM, m_sequencer, {})

`endif
