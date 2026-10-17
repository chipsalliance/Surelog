// An interface member SELECT as an instance port actual, inside a generate
// loop: the elaborated high_conn must stay an expression (a bit_select of
// the hier_path `receiver_if.valid[i]`), not collapse to the member
// variable itself re-parented under the port (tnoc's flit fifos).
interface flit_if #(parameter int CHANNELS = 2, parameter int W = 8);
  logic [CHANNELS-1:0] valid;
  logic [CHANNELS-1:0] ready;
  logic [W-1:0]        flit [CHANNELS];
  modport receiver (input valid, flit, output ready);
  modport sender   (output valid, flit, input ready);
endinterface

module fifo #(parameter int W = 8) (
  input  logic         clk, rst_n,
  input  logic         i_push,
  input  logic [W-1:0] i_data,
  input  logic         i_pop,
  output logic         o_empty,
  output logic [W-1:0] o_data
);
  always_ff @(posedge clk, negedge rst_n)
    if (!rst_n) begin o_data <= '0; o_empty <= 1'b1; end
    else if (i_push) begin o_data <= i_data; o_empty <= 1'b0; end
    else if (i_pop) o_empty <= 1'b1;
endmodule

module dut #(parameter int CHANNELS = 2) (
  input  logic clk, rst_n,
  flit_if.receiver receiver_if,
  flit_if.sender   sender_if
);
  logic [CHANNELS-1:0] empty;
  for (genvar i = 0; i < CHANNELS; ++i) begin : g
    fifo u_fifo (
      .clk     (clk),
      .rst_n   (rst_n),
      .i_push  (receiver_if.valid[i]),
      .i_data  (receiver_if.flit[i]),
      .i_pop   (sender_if.ready[i]),
      .o_empty (empty[i]),
      .o_data  (sender_if.flit[i])
    );
    assign receiver_if.ready[i] = 1'b1;
    assign sender_if.valid[i]   = ~empty[i];
  end
endmodule
