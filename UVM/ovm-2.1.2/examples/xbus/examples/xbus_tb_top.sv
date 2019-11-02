// $Id: //dvt/vtech/dev/main/ovm-tests/examples/xbus/examples/xbus_tb_top.sv#1 $
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

`define XBUS_ADDR_WIDTH 16

`include "dut_dummy.v"
`include "xbus_if.sv"

module xbus_tb_top;

  `include "xbus.svh"
  `include "test_lib.sv"

  xbus_if xi0();
  
  dut_dummy dut(
    xi0.sig_request[0],
    xi0.sig_grant[0],
    xi0.sig_request[1],
    xi0.sig_grant[1],
    xi0.sig_clock,
    xi0.sig_reset,
    xi0.sig_addr,
    xi0.sig_size,
    xi0.sig_read,
    xi0.sig_write,
    xi0.sig_start,
    xi0.sig_bip,
    xi0.sig_data,
    xi0.sig_wait,
    xi0.sig_error
  );

  initial begin
    run_test();
  end

  initial begin
    xi0.sig_reset <= 1'b1;
    xi0.sig_clock <= 1'b1;
    #51 xi0.sig_reset = 1'b0;
  end

  //Generate Clock
  always
    #5 xi0.sig_clock = ~xi0.sig_clock;

endmodule
