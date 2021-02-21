`ifdef SYNTHESIS
`define BSG_UNDEFINED_IN_SIM(val) (val)

`else
`define BSG_UNDEFINED_IN_SIM(val) ('X)
`endif

module undefined #(val_p=`BSG_UNDEFINED_IN_SIM(7)) (output [31:0] o);

assign o = val_p;

endmodule
