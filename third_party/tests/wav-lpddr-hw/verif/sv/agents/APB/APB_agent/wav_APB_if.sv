/*********************************************************************************
Copyright (c) 2021 Wavious LLC

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.

*********************************************************************************/

// TODO Describe the  wav_APB_if interface
interface wav_APB_if(input clock, input reset);

  // Control whether checks are enabled.
  bit                has_checks = 1;
  // Control whether coverage is enabled.
  bit                has_coverage = 1;

  // TODO Define the signals in wav_APB_if
  //
  // For example:
  logic              [32:0] data;

  logic  [31:0]   paddr;
  logic  [31:0]   pwdata;
  logic  [31:0]   prdata;

  logic           pclk;
  logic           preset;
  logic  [2:0]    pprot;
  // Should we use pullup?        // TODO
  // logic  psel = 0;
  // logic  penable = 0;
  // logic  pwrite = 0;
  // removed default values
  logic           psel;
  logic           penable;
  logic           pwrite;
  logic [3:0]     pstrb;
  logic           pready;
  logic           pslverr;

  assign pclk   = clock;
  assign preset = reset;

  clocking cb_drv @(posedge clock);
     default input #2ns output #2ns;
     output psel, penable, pwrite, paddr, pwdata, pprot, pstrb;
     input  prdata, pslverr;
     input  #5ns pready;
  endclocking // cb_drv

  clocking cb_slv_drv @(posedge clock);
     default input #2ns output #2ns;
     input  psel, penable, pwrite, paddr, pwdata, pprot, pstrb;
     output pready, prdata, pslverr;
  endclocking // cb_drv

  clocking cb_mon @(posedge clock);
     default input #2ns;
     input psel, penable, pwrite, paddr, pwdata, pprot, pstrb, pready, prdata, pslverr;
  endclocking // cb_mon

  modport mp_drv (input reset, clocking cb_drv);

  modport mp_slv_drv(input reset, clocking cb_slv_drv);

  modport mp_mon(input reset, clocking cb_mon);

   // TODO Implement assertions in wav_APB_if
   // For example:
   // always @(negedge sig_clock) begin
   //
   // // Read and write never true at the same time
   // assertReadOrWrite: assert property (
   //                disable iff(!has_checks)
   //                ($onehot(sig_grant) |-> !(sig_read && sig_write)))
   //                else
   //                  $error("ERR_READ_OR_WRITE\n Read and Write true at the same time");
   //
   // end

endinterface
