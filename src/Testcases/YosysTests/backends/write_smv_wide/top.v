module tristate (en, i, io, o);
    input en;
    input [3:0] i;
    inout [3:0] io;
    output [1:0] o;

    wire [3:0] io;
`ifndef BUG
	assign 	io[1:0] = (en)? i[1:0] : 1'bZ;

    assign 	io[3:2] = (i[1:0])? en : 1'bZ;

    assign o = io[2:1];
`else
	assign 	io[1:0] = (en)? ~i[1:0] : 1'bZ;

    assign 	io[3:2] = (i[1:0])? ~en : 1'bZ;

    assign o = ~io[2:1];
`endif

endmodule


module top (
input en,
input [3:0] a,
inout [3:0] b,
output [1:0] c
);

tristate u_tri (
        .en (en ),
        .i (a ),
        .io (b ),
        .o (c )
    );

endmodule
