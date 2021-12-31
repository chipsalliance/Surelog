package tl_main_pkg;
   localparam int ADDR_SPACE_DEBUG_MEM = 1;
endpackage

package dm;
   localparam int HaltAddress = 10;
   localparam logic [31:0] ExceptionAddress = HaltAddress + 2;
endpackage : dm

module top_earlgrey;
  import tl_main_pkg::*;

  rv_core_ibex #(
     .DmExceptionAddr(ADDR_SPACE_DEBUG_MEM + dm::ExceptionAddress)
  ) u_rv_core_ibex();
endmodule

module rv_core_ibex;
   parameter int unsigned DmExceptionAddr = 3;
   ibex_core #(
      .DmExceptionAddr(DmExceptionAddr)
  ) u_core();
endmodule

module ibex_core;
   parameter int unsigned DmExceptionAddr = 4;
endmodule // ibex_core
