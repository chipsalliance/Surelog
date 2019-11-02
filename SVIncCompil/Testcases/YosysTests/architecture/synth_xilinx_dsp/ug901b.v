// 8-Tap Even Symmetric Systolic FIR
//
// Source:
// https://www.xilinx.com/support/documentation/sw_manuals/xilinx2014_2/ug901-vivado-synthesis.pdf p.93
//
(* top *)
module ug901b #(parameter nbtap = 4, dsize = 16, psize = 2*dsize) (
input clk, 
input signed [dsize-1:0] datain, 
output signed [2*dsize-1:0] firout
);
wire signed [dsize-1:0] h [nbtap-1:0];
wire signed [dsize-1:0] arraydata [nbtap-1:0];
wire signed [psize-1:0] arrayprod [nbtap-1:0];
wire signed [dsize-1:0] shifterout;
reg signed [dsize-1:0] dataz [nbtap-1:0];

assign h[0] = 7;
assign h[1] = 14;
assign h[2] = -138;
assign h[3] = 129;

assign firout = arrayprod[nbtap-1]; // Connect last product to output

sfir_shifter #(dsize, nbtap) shifter_inst0 (
	clk,
	datain,
	shifterout);

generate
	genvar I;
	for (I=0; I<nbtap; I=I+1)
		if (I==0)
			sfir_even_symmetric_systolic_element #(dsize) fte_inst0 (
				clk,
				h[I],
                datain,
                shifterout,
                {32{1'b0}},
                arraydata[I],
				arrayprod[I]);
		else
			sfir_even_symmetric_systolic_element #(dsize) fte_inst (
                clk,
                h[I],
                arraydata[I-1],
                shifterout,
                arrayprod[I-1],
                arraydata[I],
                arrayprod[I]);
	endgenerate
endmodule

(* gentb_skip *) // Prevents Yosys' test_autotb from operating on this module
(* dont_touch = "yes" *)
module sfir_shifter #(parameter dsize = 16, nbtap = 4) (
     input clk, 
     input [dsize-1:0] datain, 
     output [dsize-1:0] dataout
);
(* srl_style = "srl_register" *) reg [dsize-1:0] tmp [0:2*nbtap-1];
integer i;
always @(posedge clk)
begin
    tmp[0] <= datain;
    for (i=0; i<=2*nbtap-2; i=i+1)
        tmp[i+1] <= tmp[i];
end
assign dataout = tmp[2*nbtap-1];
endmodule

(* gentb_skip *) // Prevents Yosys' test_autotb from operating on this module
module sfir_even_symmetric_systolic_element #(parameter dsize = 16) (
    input clk, 
    input signed [dsize-1:0] coeffin, datain, datazin,
    input signed [2*dsize-1:0] cascin,
    output signed [dsize-1:0] cascdata,
    output reg signed [2*dsize-1:0] cascout
);
reg signed [dsize-1:0] coeff;
reg signed [dsize-1:0] data;
reg signed [dsize-1:0] dataz;
reg signed [dsize-1:0] datatwo;
reg signed [dsize:0] preadd;
reg signed [2*dsize-1:0] product;
assign cascdata = datatwo;

always @(posedge clk)
begin
    coeff <= coeffin;
    data <= datain;
    datatwo <= data;
    dataz <= datazin;
    preadd <= datatwo + dataz;
    product <= preadd * coeff;
    cascout <= product + cascin;
end

endmodule

`ifndef _AUTOTB
module __test ;
    wire [4095:0] assert_area = "cd ug901b; flatten; select t:DSP48E1 -assert-count 4; select t:FDRE -assert-count 128; select t:SRL16E -assert-count 16; select -assert-none t:DSP48E1 t:BUFG t:FDRE t:SRL16E %% t:* %D";
endmodule
`endif

