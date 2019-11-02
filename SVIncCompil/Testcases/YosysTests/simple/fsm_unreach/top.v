module top(clk, rst, a, b, c, x, y, z);
  input clk, rst;
  input [4:0] a;
  input [4:0] b;
  input [4:0] c;
  output reg [4:0] x;
  output reg [4:0] y;
  output reg [4:0] z;
  reg [3:0] state;
  always @(posedge clk) begin
    if (rst) begin
      x <= 1;
      y <= 2;
      z <= 3;
      state <= 1;
    end else begin
      case (state)
        1: begin
`ifndef BUG
            x <= x;
            y <= b;
            z <= 1;
`else
            x <= 5'd0;
            y <= 5'd0;
            z <= 5'd0;
`endif
          end
        2: begin
            x <= a;
            y <= c;
            z <= c;
            if ((x) < (5'd3)) state <= 4;
            if ((y) < (5'd3)) state <= 3;
          end
        3: begin
            x <= y;
            y <= a;
            z <= y;
            state <= 1;
          end
        4: begin
            x <= b;
            y <= 5'd1;
            z <= 5'd2;
          end
        5: begin
            x <= 5'd1;
            y <= 5'd2;
            z <= z;
          end
        6: begin
            x <= 5'd1;
            y <= 5'd2;
            z <= z;
          end
      endcase
    end
  end
endmodule
