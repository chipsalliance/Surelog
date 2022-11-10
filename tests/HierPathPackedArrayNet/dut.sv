package rvfi_pkg;
localparam NRET = 1;
localparam ILEN = 32;

typedef struct packed {
  logic [NRET-1:0]                 trap;
} rvfi_instr_t;

endpackage

module rvfi_tracer #(
  parameter int unsigned NR_COMMIT_PORTS = 2
)(
  input rvfi_pkg::rvfi_instr_t[NR_COMMIT_PORTS-1:0]           rvfi_i
);
always_ff @(posedge clk_i) begin
  for (int i = 0; i < NR_COMMIT_PORTS; i++) begin
    if (rvfi_i[i].trap) begin
    end
  end
end  
endmodule

