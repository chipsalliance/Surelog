/*
:name: time-literals
:description: Examples of time literals
:tags: 5.8
*/

`timescale 100ps/10ps

module top();
  time a;

  initial begin
    a = 1fs;
    a = 1ps;
    a = 1ns;
    a = 1us;
    a = 1ms;
    a = 1s;

    /* real */
    a = 2.1ms;

  end;

endmodule
