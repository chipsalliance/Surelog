module tristate (en, i, o);
    input en;
    input i;    
    output [1:0] o;
    
    wire [1:0] io;

    assign	io[0] = i & ~en;
    assign	io[1] = i ? en : ~en;
		
    assign o = io;
endmodule


module top (
input en,
input a,
inout [1:0] b,
output [1:0] c
);

tristate u_tri (
        .en (en ),
        .i (a ),
        .o (c )
    );

endmodule
