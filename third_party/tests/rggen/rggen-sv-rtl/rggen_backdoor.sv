`ifdef RGGEN_ENABLE_BACKDOOR
module rggen_backdoor #(
  parameter int DATA_WIDTH  = 32
)(
  input   logic                   i_clk,
  input   logic                   i_rst_n,
  input   logic                   i_frontdoor_valid,
  input   logic                   i_frontdoor_ready,
  output  logic                   o_backdoor_valid,
  output  logic                   o_pending_valid,
  output  logic [DATA_WIDTH-1:0]  o_read_mask,
  output  logic [DATA_WIDTH-1:0]  o_write_mask,
  output  logic [DATA_WIDTH-1:0]  o_write_data,
  input   logic [DATA_WIDTH-1:0]  i_read_data,
  input   logic [DATA_WIDTH-1:0]  i_value
);
  rggen_backdoor_if backdoor_if(i_clk, i_rst_n);
  logic             pending_valid;

  assign  o_backdoor_valid      = backdoor_if.valid;
  assign  o_pending_valid       = pending_valid;
  assign  o_read_mask           = backdoor_if.read_mask;
  assign  o_write_mask          = backdoor_if.write_mask;
  assign  o_write_data          = backdoor_if.write_data;
  assign  backdoor_if.read_data = i_read_data;
  assign  backdoor_if.value     = i_value;

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      pending_valid <= '0;
    end
    else if (i_frontdoor_ready) begin
      pending_valid <= '0;
    end
    else if (backdoor_if.valid && i_frontdoor_valid) begin
      pending_valid <= '1;
    end
  end

  initial begin
    rggen_backdoor_pkg::set_backdoor_vif($sformatf("%m"), backdoor_if);
  end
endmodule
`endif
