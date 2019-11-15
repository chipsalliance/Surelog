module top(clk, a, b, reset);

   input       clk, a, b, reset;

   (* keep *)
   wire        eq_a_b;
   (* keep *)
   reg [15:0]  num_a;
   (* keep *)
   reg [15:0]  num_b;

   always @(posedge clk)
     begin
	      if (reset) begin
	         num_a <= 16'b0;
	         num_b <= 16'b0;
	      end else begin
	         num_a <= num_a + {15'b0, a};
	         num_b <= num_b + {15'b0, b};
	      end
     end

   assign eq_a_b = (num_a == num_b);

endmodule // top
