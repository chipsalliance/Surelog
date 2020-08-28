module top();

	
	
	initial begin
	
		
		forever @(posedge clock) begin
			if (ref != dout) begin
				$display("ERROR at %t: A=%b B=%b OP=%b OUT=%b (expected %b)",
						$time, dinA, dinB, opcode, dout, ref);
				$stop;
			end

			
		end
	end


	
endmodule