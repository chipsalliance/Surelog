module tristate (en, i, o);
    input en;
    input i;
    output reg o;

    always @(en or i)
		begin
			case (en)
`ifndef BUG 
				1:o <= i;
`else
				1:o <= ~i;
`endif
				default :o <= 1'bZ;
			endcase
		end
endmodule


module top (
input en,
input a,
output b
);

tristate u_tri (
        .en (en ),
        .i (a ),
        .o (b )
    );

endmodule
