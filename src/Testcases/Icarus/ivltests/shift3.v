
module main;

   reg [7:0] xu;
   reg signed [7:0] xs;

   initial begin
      xu = 8'b1100_0000;
      xs = 8'b1100_0000;

      xu = xs >>> 3;
      xs = xu >>> 3;

      if (xu !== 8'b0001_1000) begin
	 $display("FAILED -- xu = xs >>> 3 failed. xu=%b", xu);
	 $finish;
      end

      if (xs !== 8'b0001_1000) begin
	 $display("FAILED -- xs = xu >>> 3 failed. xs=%b", xs);
	 $finish;
      end

      $display("PASSED");
   end // initial begin

endmodule // main
