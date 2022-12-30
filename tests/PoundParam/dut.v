// POSITIVE-EDGE TRIGGERED FLOP with SCAN, RESET
module dffr (din, clk, rst, q, se, si, so);
// synopsys template

parameter SIZE = 1;

input	[SIZE-1:0]	din ;	// data in

input			clk ;	// clk or scan clk
input			rst ;	// reset

output	[SIZE-1:0]	q ;	// output

input			se ;	// scan-enable
input	[SIZE-1:0]	si ;	// scan-input
output	[SIZE-1:0]	so ;	// scan-output

reg 	[SIZE-1:0]	q ;

`ifdef NO_SCAN
always @ (posedge clk)
	q[SIZE-1:0]  <= ((rst) ? {SIZE{1'b0}}  : din[SIZE-1:0] );
`else

// Scan-Enable dominates
always @ (posedge clk)

	q[SIZE-1:0]  <= se ? si[SIZE-1:0] : ((rst) ? {SIZE{1'b0}}  : din[SIZE-1:0] );

assign so[SIZE-1:0] = q[SIZE-1:0] ;
`endif

endmodule // dffr

module test(pv1,pv2,next_pv,clk,reset,se);
output [3:0] pv1,pv2,next_pv;
input clk,reset,se;

 dffr #4  park_reg(.din  (next_pv[3:0]),
                    .clk  (clk),
                    .q    (pv1[3:0]),
                    .rst  (reset),
                    .se   (se), .si(), .so());

 dffr #4 logic(.din  (next_pv[3:0]),
                    .clk  (clk),
                    .q    (pv2[3:0]),
                    .rst  (reset),
                    .se   (se), .si(), .so());
                    
endmodule
