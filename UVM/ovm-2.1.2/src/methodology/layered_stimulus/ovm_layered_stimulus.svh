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

`ifndef OVM_LAYERED_STIMULUS
`define OVM_LAYERED_STIMULUS

typedef ovm_sequence_base ovm_scenario_base;
typedef ovm_sequencer_base ovm_scenario_controller_base;

`include "methodology/layered_stimulus/ovm_scenario_driver.svh"
`include "methodology/layered_stimulus/ovm_scenario_controller.svh"
`include "methodology/layered_stimulus/ovm_scenario.svh"
  
`endif
