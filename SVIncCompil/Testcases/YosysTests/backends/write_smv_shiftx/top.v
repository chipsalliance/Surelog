
// VERIFIC-SKIP

module top(a, y);

input signed [4:0] a;
output signed y;

integer signed i = 0, j = 0;
reg signed [31:0] lut;

initial begin
	for (i = 0; i < 32; i = i+1) begin
		lut[i] = i > 1;
		for (j = 2; j*j <= i; j = j+1)
			if (i % j == 0)
				lut[i] = 0;
	end
end

assign y = lut[a];

endmodule
