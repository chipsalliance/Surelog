module decode1_1(input clk,
		 input 	       rst,
		 input [31:0]  in_count,
		 input 	       in_valid,
		 output        in_ready,

		 input 	       out_ready,
		 output        out_valid);

   reg [31:0] 		       r_remaining_count;
   reg 			       r_valid;
   reg 			       r_ready;

   assign out_valid = r_valid;
   assign in_ready = r_ready;

   always @(posedge clk) begin
      if (rst) begin
	 r_remaining_count <= 0;
	 r_valid <= 0;
	 r_ready <= 0;
      end else begin
	 if (r_remaining_count == 0) begin
	    if (r_ready && in_valid) begin
	       r_remaining_count <= in_count;
	       r_valid <= in_count != 0;
	       r_ready <= 0;
	    end else begin
	       r_ready <= 1;
	       r_valid <= 0;
	    end
	 end else begin
	    r_valid <= !(r_remaining_count == 1 && out_ready && out_valid);
	    r_ready <= 0;

	    if (out_valid && out_ready) begin
	       r_remaining_count <= r_remaining_count - 1;
	    end
	 end
      end
   end

endmodule // decode1_1

module top(input clk);
   wire        out_valid;
   wire [31:0] out_data;
   wire        out_ready = 1'b1;

   reg [31:0]  cycles;
   wire        rst = (cycles < 3);

   wire        in_ready;

   reg [31:0]  test_counts [0:1];
   reg [31:0]  test_index;
   wire        in_valid = (test_index < 1) && (cycles > 2);

   reg [9:0]   out_data_index;

   always @(posedge clk)
     begin
	cycles <= cycles + 1;
     end

   always @(posedge clk)
     begin
	if (cycles < 1) begin
	   test_counts[cycles] <= $anyseq;
	end
     end

   initial begin
      cycles  = 0;

      test_index = 0;
   end

   decode1_1 decoder(clk, rst,
		 test_counts[test_index],
		 in_valid,
		 in_ready,

		 out_ready,
		 out_valid);

   always @(posedge clk) begin
      if (!rst) begin
	 assert(out_data_index <= 0);

	 if (in_valid && in_ready) begin
	    test_index <= test_index + 1;
	 end
	 if (out_ready && out_valid) begin
	    out_data_index <= out_data_index + 1;
	 end
      end
   end // always @ (posedge clk)
endmodule
