module gen_test3(a, b, sel, y, z);

input [3:0] a, b;
input sel;
output [3:0] y, z;

genvar i;
generate
	for (i=0; i < 2; i=i+1)
		assign y[i] = sel ? a[i] : b[i], z[i] = sel ? b[i] : a[i];
	for (i=0; i < 2; i=i+1) begin
		if (i == 0)
			assign y[2] = sel ? a[2] : b[2];
		else
			assign z[2] = sel ? a[2] : b[2];
		case (i)
		default:
			assign z[3] = sel ? a[3] : b[3];
		0:
			assign y[3] = sel ? a[3] : b[3];
		endcase
	end
endgenerate
endmodule
