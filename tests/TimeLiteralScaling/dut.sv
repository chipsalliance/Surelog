// A time literal is a value in the enclosing module's time unit, rounded to
// its precision (LRM 5.8 / 3.14).  Under 100ps/10ps: 1ns = 10, 1us = 10000,
// 1ms = 10000000, the real 2.1ms = 21000000, 1_0ns = 100.  The second module
// declares its own `timeunit`; the third has none (1ns default).
`timescale 100ps/10ps
module top(output logic [63:0] t_ns, output logic [63:0] t_us, output logic [63:0] t_ms,
           output logic [63:0] t_real, output logic [63:0] t_sep);
  assign t_ns   = 1ns;
  assign t_us   = 1us;
  assign t_ms   = 1ms;
  assign t_real = 2.1ms;
  assign t_sep  = 1_0ns;
endmodule
module unit_decl(output logic [63:0] t_ns, output logic [63:0] t_half);
  timeunit 1ns / 1ps;
  assign t_ns   = 1ns;      // 1
  assign t_half = 0.5us;    // 500
endmodule
