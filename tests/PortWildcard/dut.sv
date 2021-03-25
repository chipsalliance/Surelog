
  
module rvdff #( parameter WIDTH=1 )
   (
     input logic [WIDTH-1:0] din,
     input logic           clk,
     input logic                   rst_l,

     output logic [WIDTH-1:0] dout
     );


endmodule

module dut();
input logic                   rst_l;
  rvdff #(2)  freezerfpc_ff (.*,  .clk(free_clk),
                                .din({rfpc_postsync_in, dma_mem_dccm_req}),
                                .dout({rfpc_postsync, dma_mem_dccm_req_f}));
                                                                    
endmodule    
