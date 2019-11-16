module testbench;
	reg clock;

	initial begin
		// $dumpfile("testbench.vcd");
		// $dumpvars(0, testbench);

		#5 clock = 0;
		repeat (10000) begin
			#5 clock = 1;
			#5 clock = 0;
		end

		$display("OKAY");
	end

	reg  [31:0] dinA;
	reg  [31:0] dinB;
	reg  [2:0]  opcode;
	wire [31:0] dout;

	top uut (
		.clock  (clock ),
		.dinA   (dinA  ),
		.dinB   (dinB  ),
		.opcode (opcode),
		.dout   (dout  )
	);

	reg [31:0] ref;

	always @(posedge clock) begin
		case (opcode)
		0: ref <= dinA + dinB;
		1: ref <= dinA - dinB;
		2: ref <= dinA >> dinB;
		3: ref <= $signed(dinA) >>> dinB;
		4: ref <= dinA << dinB;
		5: ref <= dinA & dinB;
		6: ref <= dinA | dinB;
		7: ref <= dinA ^ dinB;
		endcase
	end

	reg [127:0] rngstate = 1;
	reg [63:0] rng;

	task rngnext;
		// xorshift128plus
		reg [63:0] x, y;
		begin
			{y, x} = rngstate;
			rngstate[63:0] = y;
			x ^= x << 23;
			rngstate[63:0] = x ^ y ^ (x >> 17) ^ (y >> 26);
			rng = rngstate[63:0] + y;
		end
	endtask

	initial begin
		dinA <= 1;
		dinB <= 2;
		opcode <= 0;

		repeat (100)
			rngnext;

		forever @(posedge clock) begin
			if (ref != dout) begin
				$display("ERROR at %t: A=%b B=%b OP=%b OUT=%b (expected %b)",
						$time, dinA, dinB, opcode, dout, ref);
				$stop;
			end

			dinA <= rng;
			rngnext;

			dinB <= rng;
			rngnext;

			opcode <= rng;
			rngnext;
		end
	end
endmodule
