// $Id: //dvt/vtech/dev/main/ovm/src/methodology/methodology.svh#18 $
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
//------------------------------------------------------------------------------

`ifndef OVM_METH_SVH
`define OVM_METH_SVH

  `include "methodology/ovm_pair.svh"
  `include "methodology/ovm_policies.svh"
  `include "methodology/ovm_in_order_comparator.svh"
  `include "methodology/ovm_algorithmic_comparator.svh"
  `include "methodology/ovm_random_stimulus.svh"
  `include "methodology/ovm_subscriber.svh"

  `include "methodology/sequences/ovm_sequence_item.svh"
  `include "methodology/sequences/ovm_sequencer_base.svh"
  `include "methodology/sequences/ovm_sequencer_analysis_fifo.svh"
  `include "methodology/sequences/ovm_sequencer_param_base.svh"
  `include "methodology/sequences/ovm_sequencer.svh"
  `include "methodology/sequences/ovm_push_sequencer.svh"
  `include "methodology/sequences/ovm_sequence_base.svh"
  `include "methodology/sequences/ovm_sequence.svh"
  `include "methodology/sequences/ovm_sequence_builtin.svh"

  `include "methodology/ovm_meth_defines.svh"

  `include "methodology/ovm_monitor.svh"
  `include "methodology/ovm_driver.svh"
  `include "methodology/ovm_push_driver.svh"
  `include "methodology/layered_stimulus/ovm_layered_stimulus.svh"
  `include "methodology/ovm_scoreboard.svh" 
  `include "methodology/ovm_agent.svh"
  `include "methodology/ovm_env.svh"
  `include "methodology/ovm_test.svh"

  typedef ovm_sequence  #(ovm_sequence_item, ovm_sequence_item) ovm_default_sequence_type;
  typedef ovm_sequencer #(ovm_sequence_item, ovm_sequence_item) ovm_default_sequencer_type;
  typedef ovm_driver    #(ovm_sequence_item, ovm_sequence_item) ovm_default_driver_type;
  typedef ovm_sequencer_param_base #(ovm_sequence_item, ovm_sequence_item) ovm_default_sequencer_param_type;

`endif //OVM_METH_SVH
