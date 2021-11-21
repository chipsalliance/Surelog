//------------------------------------------------------------------------------
//  Copyright 2017 Taichi Ishitani
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
`ifndef TVIP_CLOCK_IF_SV
`define TVIP_CLOCK_IF_SV

`include  "tvip_common_macros.svh"

interface tvip_clock_if ();
  timeunit      1ns;
  timeprecision `TVIP_TIME_PRECISION;

  bit       started     = 0;
  realtime  half_period = 0ns;
  bit       clk         = 0;
  bit       clk_p;
  bit       clk_n;

  assign  clk_p =  clk;
  assign  clk_n = ~clk;

  always @(posedge started) begin
    while (started) begin
      #(half_period);
      clk ^= 1;
    end
  end

  function automatic void start(realtime period_ns);
    set_period(period_ns);
    started = 1;
  endfunction

  function automatic void set_period(realtime period_ns);
    half_period = period_ns / 2.0;
  endfunction

  function automatic void stop();
    half_period = 0ns;
    started     = 0;
  endfunction
endinterface
`endif
