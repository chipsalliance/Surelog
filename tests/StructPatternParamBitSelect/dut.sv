// A bit-select of a parameter whose value is a STRUCT assignment pattern
// selects a BIT of the packed value, not a member of the pattern
// (cv32e40x / cv32e40s cs_registers: `RESETVALUE[i]` took the pattern's
// i-th member, both in an assign and in an if-generate condition).
// Expected: o == 32'h1800 and g == 32'h1810.
package p;
  typedef struct packed {
    logic [18:0] hi;
    logic [12:11] mpp;
    logic [10:9] vs;
    logic [8:0] lo;
  } st_t;
  parameter st_t RV = '{mpp: 2'b11, default: 'b0};
  parameter st_t RG = '{mpp: 2'b11, lo: 9'h010, default: 'b0};
endpackage
module csr #(parameter bit [31:0] RESETVALUE = '0) (output logic [31:0] q);
  for (genvar i = 0; i < 32; i++) begin : gen_csr
    assign q[i] = RESETVALUE[i];
  end
endmodule
module csr_gen #(parameter bit [31:0] RESETVALUE = '0) (output logic [31:0] q);
  for (genvar i = 0; i < 32; i++) begin : gen_csr
    if (RESETVALUE[i] == 1'b1) begin : g1
      assign q[i] = 1'b1;
    end else begin : g0
      assign q[i] = 1'b0;
    end
  end
endmodule
module dut(output logic [31:0] o, output logic [31:0] g);
  csr #(.RESETVALUE(p::RV)) u (.q(o));
  csr_gen #(.RESETVALUE(p::RG)) v (.q(g));
endmodule
