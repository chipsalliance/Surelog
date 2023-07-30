module rggen_bit_field_w01trg #(
  parameter bit TRIGGER_VALUE = '0,
  parameter int WIDTH         = 1
)(
  input   logic                 i_clk,
  input   logic                 i_rst_n,
  rggen_bit_field_if.bit_field  bit_field_if,
  input   logic [WIDTH-1:0]     i_value,
  output  logic [WIDTH-1:0]     o_trigger
);
  logic [WIDTH-1:0] trigger;

  assign  bit_field_if.read_data  = i_value;
  assign  bit_field_if.value      = trigger;
  assign  o_trigger               = trigger;

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      trigger <= '0;
    end
    else if (bit_field_if.valid) begin
      trigger <= get_trigger(
        bit_field_if.write_mask, bit_field_if.write_data
      );
    end
    else if (trigger != '0) begin
      trigger <= '0;
    end
  end

  function automatic logic [WIDTH-1:0] get_trigger(
    logic [WIDTH-1:0] mask,
    logic [WIDTH-1:0] write_data
  );
    if (TRIGGER_VALUE) begin
      return mask & write_data;
    end
    else begin
      return mask & (~write_data);
    end
  endfunction
endmodule
