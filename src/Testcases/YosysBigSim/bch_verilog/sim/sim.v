`timescale 1ns / 1ps

module sim #(
	parameter N = 15,
	parameter K = 5,
	parameter T = 3,
	parameter OPTION = "SERIAL"
) (
	input clk,
	input reset,
	input [K-1:0] data_in,
	input [N-1:0] error,
	input encode_start,
	output ready,
	output encoded_penult,
	output output_valid,
	output reg wrong_now = 0,
	output reg wrong = 0,
	output [K-1:0] data_out
);

`include "bch.vh"

localparam TCQ = 1;
localparam M = n2m(N);
if (OPTION != "SERIAL" && OPTION != "PARALLEL")
	illegal_option_value u_iov();

reg [K-1:0] encode_buf = 0;
reg [K-1:0] decode_buf = 0;
reg [N-1:0] flip_buf = 0;
reg [K-1:0] current_buf = 0;
reg [K-1:0] compare_buf1 = 0;
reg [K-1:0] compare_buf2 = 0;
reg last_data_valid = 0;

wire decIn;
wire new_wrong;
wire encoded_data;
wire decoded_data;
wire encoded_first;
wire encoded_last;
wire decoder_in;

wire first = !last_data_valid && output_valid;

bch_encode #(N, K, T, OPTION) u_bch_encode(
	.clk(clk),
	.globrst(reset),
	.start(encode_start),
	.data_in(encode_start ? data_in[0] : encode_buf[1]),
	.data_out(encoded_data),
	.first(encoded_first),
	.last(encoded_last),
	.penult(encoded_penult)
);

bch_decode #(N, K, T, OPTION) u_bch_decode(
	.clk(clk),
	.globrst(reset),
	.start(encoded_first),
	.ready(ready),
	.data_in(decoder_in),
	.output_valid(output_valid),
	.data_out(decoded_data)
);

assign decoder_in = (encoded_data ^ flip_buf[0]) && !reset;
assign new_wrong = ((decoded_data !== (first ? compare_buf1[0] : compare_buf2[0])) && !reset && output_valid) || ((output_valid === 1'bx) || (output_valid === 1'bz));
assign data_out = decode_buf;

always @(posedge clk) begin
	last_data_valid <= #TCQ output_valid;
	encode_buf <= #TCQ encode_start ? data_in : {1'b0, encode_buf[K-1:1]};
	flip_buf <= #TCQ encode_start ? error : {1'b0, flip_buf[N-1:1]};
	if (encode_start)
		current_buf <= #TCQ data_in;

	if (encoded_last)
		compare_buf1 <= #TCQ current_buf;

	if (first)
		compare_buf2 <= #TCQ {1'b0, compare_buf1[K-1:1]};
	else if (output_valid)
		compare_buf2 <= #TCQ {1'b0, compare_buf2[K-1:1]};

	if (output_valid)
		decode_buf <= #TCQ {decoded_data, decode_buf[K-1:1]};
	if (reset)
		wrong <= #TCQ 1'b0;
	else if (new_wrong)
		wrong <= #TCQ 1'b1;
	wrong_now <= #TCQ new_wrong;


end

endmodule
