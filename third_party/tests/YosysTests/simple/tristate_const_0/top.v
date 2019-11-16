module tristate (en, i, o);
    input en;
    input i;
    output reg o;

    always @(en or i)
`ifndef BUG 	
		o <= (en)? i : 1'bZ;
`else	
		o <= (en)? ~i : 1'bZ;
`endif
endmodule


module top (
input en,
input a,
output b
);

tristate u_tri (
        .en (1'b0 ),
        .i (a ),
        .o (b )
    );

endmodule
