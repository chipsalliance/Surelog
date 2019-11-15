/*
module top () ;
timeunit 100ps;
timeprecision 1ps;
endmodule
*/

module bottom1 (input a, input b) ;
 timeunit 10ps;
 timeprecision 1ps;
 bottom2 u1 (a[0], b);
 bottom3 u2 (a[0], b);

 my_interface my_interface(.*);

endmodule

module bottom2 (input a, input b) ;
not (b, a);
endmodule



`timescale 100ps/10ps

module bottom3 () ;

 ddr \g_datapath:0:g_io 
    (
      .capture (capture),
      .clk (clk)
    );



endmodule



















































`timescale 100ps/10ps

module bottom4 () ;
 ddr \g_datapath:0:g_io 
    (
      .capture (capture),
      .clk (clk)
    );



endmodule

