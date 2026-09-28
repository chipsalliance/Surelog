package pk;
  typedef struct packed { logic [14:0] DEPTH; logic [7:0] ADDR_HI; } cfg_t;
  localparam cfg_t CFG = '{DEPTH: 15'd256, ADDR_HI: 8'd9};
endpackage
module dut import pk::*; #(parameter cfg_t pt = CFG) (
  input  logic [1:0] en,
  input  logic [7:0] addr,
  output logic [511:0] wr
);
  for (genvar i = 0; i < 2; i++) begin : BANKS
    wire [255:0] wr0;
    assign wr0 = pt.DEPTH'(en[i] << addr);
    assign wr[i*256 +: 256] = wr0;
  end
endmodule
module top import pk::*; (input logic [1:0] en, input logic [7:0] addr, output logic [511:0] wr);
  dut #(.pt(CFG)) u (.en(en), .addr(addr), .wr(wr));
endmodule
