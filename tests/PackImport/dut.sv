

package ibex_pkg;

typedef enum logic [6:0] {
  OPCODE_LOAD     = 7'h03,
  OPCODE_LUI      = 7'h37
} opcode_e;
endpackage // ibex_pkg

package ibex_tracer_pkg;
import ibex_pkg::*;
parameter logic [31:0] INSN_LUI = { 25'h?, {OPCODE_LUI  }};
endpackage

   

module top(input clk_i, output logic [31:0] o1);
import ibex_pkg::*;
endmodule // top

