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


class sequencer_analysis_fifo #(type RSP = ovm_sequence_item) extends tlm_fifo #(RSP);

  ovm_analysis_imp #(RSP, sequencer_analysis_fifo #(RSP)) analysis_export;
  ovm_sequencer_base sequencer_ptr;

  function new (string name, ovm_component parent = null);
    super.new(name, parent, 0);
    analysis_export = new ("analysis_export", this);
  endfunction

  function void write(input RSP t);
    if (sequencer_ptr == null)
      ovm_report_fatal ("SEQRNULL", "The sequencer pointer is null when attempting a write", OVM_NONE);
    sequencer_ptr.analysis_write(t);
  endfunction // void
endclass
