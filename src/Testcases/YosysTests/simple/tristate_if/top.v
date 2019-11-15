module tribuf (en, i, o);
    input en;
    input i;
    output reg o;

    always @*
		begin
			if (en)
`ifndef BUG
				o = i;
`else	
				o = ~i;
`endif
			else
				o = 1'bZ;
		end
endmodule


module top (
input en,
input a,
output b
);

tribuf u_tri (
        .en (en ),
        .i (a ),
        .o (b )
    );

endmodule
