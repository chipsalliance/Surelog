
module rvdffe 
   (input  logic [32:0] din);
endmodule // rvdffe

module dut ();

   logic signed [32:0]  rs2_ext_in;
        
   rvdffe  i_b_x_ff         (.din(rs2_ext_in[32:0] ));

endmodule

