// $Id: //dvt/vtech/dev/main/ovm-tests/examples/xbus/sv/xbus.svh#1 $
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


`ifndef XBUS_SVH
`define XBUS_SVH

`ifdef USE_SVPP
`include "ovm.svh"
`else
import ovm_pkg::*;
`include "ovm_macros.svh"
`endif

`include "xbus_transfer.sv"

`include "xbus_master_monitor.sv"
`include "xbus_master_sequencer.sv"
`include "xbus_master_driver.sv"
`include "xbus_master_agent.sv"

`include "xbus_slave_monitor.sv"
`include "xbus_slave_sequencer.sv"
`include "xbus_slave_driver.sv"
`include "xbus_slave_agent.sv"

`include "xbus_bus_monitor.sv"

`include "xbus_env.sv"

`endif // XBUS_SVH
