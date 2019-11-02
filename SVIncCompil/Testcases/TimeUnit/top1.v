
interface my_interface(
  input clock,
  input select,
  input [3:0] data);
  
  clocking cb @(posedge clock);
    input select, data;
  endclocking
endinterface
 




















module splice1();
endmodule
























































































module splice1();
endmodule






































































module splice1();
endmodule

























































module splice1();
endmodule










module top () ;
timeunit 100ps;
timeprecision 1ps;
bottom1 u1 ();
endmodule

 
module bottom1 () ;
timeunit 10ps;
timeprecision 1ps;
endmodule

module bottom2 () ;
 
 
endmodule


module middle ();
  timeunit 10ps;
  timeprecision 1ps;
  wire a, b, c;
  module nested;
    assign c = a & b;
  endmodule
endmodule



`timescale 100ps/10ps


module bottom3 () ;
bottom4 u3();
bottom4 u4();
bottom4 u5();
endmodule

