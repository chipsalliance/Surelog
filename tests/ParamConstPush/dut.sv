package base_pkg;
localparam logic [1:0]  BASE   = 2'b00;
localparam logic [1:0]  USAGE  = BASE | 2'b01;
endpackage

package error_pkg;
localparam logic [1:0]  FROM_USAGE = base_pkg::USAGE;
endpackage

module top import error_pkg::*; #() ();
endmodule
