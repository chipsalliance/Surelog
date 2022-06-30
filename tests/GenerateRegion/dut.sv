module oh_delay
#(parameter N        = 1,               // width of data
  parameter MAXDELAY = 4,               // maximum delay cycles
  parameter M        = $clog2(MAXDELAY) // delay selctor
  )
 (
 
  );

 genvar 	    i;
 generate
    always @ (posedge clk)
      sync_pipe[0]<=in[N-1:0];
    for(i=1;i<MAXDELAY;i=i+1) begin: gen_pipe
       always @ (posedge clk)
         sync_pipe[i]<=sync_pipe[i-1];
    end
 endgenerate

endmodule



module shift(a,s,z);
parameter    width_a = 4;
parameter    signd_a = 1;
parameter    width_s = 2;
parameter    width_z = 8;

input [width_a-1:0] a;
input [width_s-1:0] s;
output [width_z -1:0] z;

generate if ( signd_a )
begin: SGNED
  assign z = fshl_s(a,s,a[width_a-1]);
end
else
begin: UNSGNED
  assign z = fshl_s(a,s,1'b0);
end
endgenerate
endmodule


module gen_test9;
        wire [1:0] w = 2'b11;
        generate
                begin : A
                        wire [1:0] x;
                        generate
                        begin : B
                                wire [1:0] y = 2'b00;
                        end
                        endgenerate
                        generate
                        begin : C
                                wire [1:0] z = 2'b01;
                        end
                        endgenerate
                        assign x = B.y ^ 2'b11 ^ C.z;
                end
        endgenerate
endmodule // gen_test9




module dut ();
        test #(
                .Width(32),
                .DataBitsPerMask(8)
        ) t ();
endmodule

module test #(
parameter  int Width           = 32,
parameter  int DataBitsPerMask = 2
) ();
        localparam int MaskWidth = Width / DataBitsPerMask;

generate 
   for (i = 0; i < MaskWidth; i++) begin
      G1 u();
   end
endgenerate 

endmodule




module oh_rsync
  #(parameter SYNCPIPE = 2,        // number of sync stages
    parameter SYN      = "TRUE",   // true=synthesizable
    parameter TYPE     = "DEFAULT" // scell type/size
    )
   (
  
    );

   generate
      if(SYN == "TRUE")
	begin
	   reg [SYNCPIPE-1:0] sync_pipe;
	   always @ (posedge clk or negedge nrst_in)
	     if(!nrst_in)
	       sync_pipe[SYNCPIPE-1:0] <= 'b0;
	     else
	       sync_pipe[SYNCPIPE-1:0] <= {sync_pipe[SYNCPIPE-2:0],1'b1};
	   assign nrst_out = sync_pipe[SYNCPIPE-1];
	end
      else
	begin
	   asic_rsync #(.TYPE(TYPE),
			.SYN(SYN),
			.SYNCPIPE(SYNCPIPE))
	   asic_rsync (.clk(clk),
		       .nrst_in(nrst_in),
		       .nrst_out(nrst_out));
	end
   endgenerate
endmodule // oh_rsync

