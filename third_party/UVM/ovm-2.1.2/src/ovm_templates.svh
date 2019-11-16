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

// This file is used to allow template objects to be used in multiple scopes
// where the definitions and specializations do not need to be shared between
// The scopes. This is only needed if a simulator does not fully supported
// templated types in seperate scopes.

`include "ovm_macros.svh"

`ifndef USE_PARAMETERIZED_WRAPPER

`include "tlm/tlm.svh"

`include "methodology/ovm_pair.svh"
`include "methodology/ovm_policies.svh"
`include "methodology/ovm_in_order_comparator.svh"
`include "methodology/ovm_algorithmic_comparator.svh"
`include "methodology/ovm_random_stimulus.svh"
`include "methodology/ovm_subscriber.svh"
`include "methodology/ovm_push_driver.svh"
`include "methodology/ovm_driver.svh"
`include "methodology/sequences/ovm_sequencer_analysis_fifo.svh"
`include "methodology/sequences/ovm_sequencer_param_base.svh"
`include "methodology/sequences/ovm_push_sequencer.svh"
`include "methodology/sequences/ovm_sequencer.svh"
`include "methodology/sequences/ovm_sequence.svh"

`endif
