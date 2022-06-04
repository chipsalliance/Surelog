
package riscv_isa_pkg;

typedef struct packed {
  struct packed {
    logic         rs1;  // read enable register source 1
    logic         rs2;  // read enable register source 2
    logic         rd;   // write enable register destination
  } e;
  struct packed {
    logic [5-1:0] rs1;  // address register source 1 (read)
    logic [5-1:0] rs2;  // address register source 2 (read)
    logic [5-1:0] rd ;  // address register destination (write)
  } a;
} gpr_t;

// control structure
// TODO: change when Verilator supports unpacked structures
typedef struct packed {
  
  gpr_t      gpr;     // GPR control signals
 
} ctl_t;


endpackage: riscv_isa_pkg

module r5p_wbu (input  ctl_t  ctl);
  import riscv_isa_pkg::*;
  reg wen;
  always_ff @(posedge clk)
  if (rst) begin
    wen <= ctl.gpr.e.rd;
  end


endmodule // r5p_wbu
