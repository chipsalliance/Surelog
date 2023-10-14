module left_rotate_assertions (
    input clk,
    input rst_n,
    input [31:0] word_in,
    input [4:0] rotate_by, // 5 bits can represent values from 0 to 31
    input [31:0] rotated
);

  // Initialization check
  initial begin
    @(posedge clk);
    if (!rst_n) begin
      assert(rotated == 0);
    end
  end

  // Valid Rotation
  property p_valid_rotation;
    @(posedge clk) (!rst_n) |-> (rotated == (word_in << rotate_by) | (word_in >> (32-rotate_by)));
  endproperty
  a_valid_rotation: assert property(p_valid_rotation);

  // Rotation Range
  property p_rotation_range;
    @(posedge clk) (!rst_n) |-> (rotate_by <= 5'd31);
  endproperty
  a_rotation_range: assert property(p_rotation_range);

  // No Rotation
  property p_no_rotation;
    @(posedge clk) (!rst_n && rotate_by == 0) |-> (rotated == word_in);
  endproperty
  a_no_rotation: assert property(p_no_rotation);

endmodule

bind left_rotation left_rotate_assertions u_left_rotate_assertions (
    .clk(clk),
  .rst_n(reset),
  .word_in(in_data),
    .rotate_by(),
  .rotated(out_data)
);
