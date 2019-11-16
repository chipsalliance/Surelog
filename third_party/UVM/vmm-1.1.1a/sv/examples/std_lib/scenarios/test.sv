// $Id: //dvt/vtech/dev/main/ovm/examples/sequence/test.sv#3 $
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
module test;

  `include "vmm.sv"
  `include "simple_item.sv"
  `include "simple_sequencer.sv"
  `include "simple_driver.sv"
  `include "simple_seq_lib.sv"

  simple_item_scenario_gen sequencer;
  simple_driver driver;

  initial begin
     driver = new("driver");
     sequencer = new("sequencer", "", driver.in_chan);
     begin
        simple_seq_sub_seqs seq;
        seq = new;
        sequencer.scenario_set[0] = seq;
        sequencer.stop_after_n_scenarios = 1;
     end
     driver.start_xactor();
     sequencer.start_xactor();
  end

  initial begin
    #2000;
  end

endmodule
