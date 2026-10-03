package id_pkg;
  localparam logic [10:0] MFR = {4'd12, 7'b110_1111};
  localparam logic [3:0]  VER = 4'h1;
  localparam logic [11:0] PART = 12'h0;
  localparam logic [31:0] IDCODE = { VER, PART, 4'h1, MFR, 1'b1 };
endpackage
module tap #(parameter logic [31:0] IdcodeValue = 32'h00000001) (input logic tck, input logic trst_n, input logic sel, output logic [31:0] q);
  always_ff @(posedge tck, negedge trst_n)
    if (!trst_n) q <= IdcodeValue; else if (sel) q <= IdcodeValue; else q <= {q[30:0], 1'b0};
endmodule
module dmi #(parameter logic [31:0] IdcodeValue = 32'h00000DB3) (input logic tck, input logic trst_n, input logic sel, output logic [31:0] q);
  tap #(.IdcodeValue(IdcodeValue)) i_tap (.tck, .trst_n, .sel, .q);
endmodule
module rvdm #(parameter logic [31:0] IdcodeValue = 32'h0000_0001) (input logic tck, input logic trst_n, input logic sel, output logic [31:0] q);
  dmi #(.IdcodeValue(IdcodeValue)) dap (.tck, .trst_n, .sel, .q);
endmodule
module dut #(parameter logic [31:0] RvDmIdcodeValue = id_pkg::IDCODE) (input logic tck, input logic trst_n, input logic sel, output logic [31:0] q);
  rvdm #(.IdcodeValue(RvDmIdcodeValue)) u_rv_dm (.tck, .trst_n, .sel, .q);
endmodule
