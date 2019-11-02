
module vscale_hasti_bridge(
                           output [32-1:0]  haddr,
                           output                          hwrite,
                           output [3-1:0]  hsize,
                           output [3-1:0] hburst,
                           output                          hmastlock,
                           output [4-1:0]  hprot,
                           output [2-1:0] htrans,
                           output [32-1:0]   hwdata,
                           input [32-1:0]    hrdata,
                           input                           hready,
                           input [1-1:0]   hresp,
                           input                           core_mem_en,
                           input                           core_mem_wen,
                           input [3-1:0]   core_mem_size,
                           input [32-1:0]   core_mem_addr,
                           input [32-1:0]    core_mem_wdata_delayed,
                           output [32-1:0]   core_mem_rdata,
                           output                          core_mem_wait,
                           output                          core_badmem_e
                           );


   assign haddr = core_mem_addr;
   assign hwrite = core_mem_en && core_mem_wen;
   assign hsize = core_mem_size;
   assign hburst = 3'd0;
   assign hmastlock = 1'b0;
   assign hprot = 4'd0;
   assign htrans = core_mem_en ?  2'd2: 2'd0;
   assign hwdata = core_mem_wdata_delayed;
   assign core_mem_rdata = hrdata;
   assign core_mem_wait = ~hready;
   assign core_badmem_e = hresp == 1'd1;

endmodule // vscale_hasti_bridge

