`include "vscale_hasti_constants.vh"

module vscale_hasti_bridge(
                           output [`HASTI_ADDR_WIDTH-1:0]  haddr,
                           output                          hwrite,
                           output [`HASTI_SIZE_WIDTH-1:0]  hsize,
                           output [`HASTI_BURST_WIDTH-1:0] hburst,
                           output                          hmastlock,
                           output [`HASTI_PROT_WIDTH-1:0]  hprot,
                           output [`HASTI_TRANS_WIDTH-1:0] htrans,
                           output [`HASTI_BUS_WIDTH-1:0]   hwdata,
                           input [`HASTI_BUS_WIDTH-1:0]    hrdata,
                           input                           hready,
                           input [`HASTI_RESP_WIDTH-1:0]   hresp,
                           input                           core_mem_en,
                           input                           core_mem_wen,
                           input [`HASTI_SIZE_WIDTH-1:0]   core_mem_size,
                           input [`HASTI_ADDR_WIDTH-1:0]   core_mem_addr,
                           input [`HASTI_BUS_WIDTH-1:0]    core_mem_wdata_delayed,
                           output [`HASTI_BUS_WIDTH-1:0]   core_mem_rdata,
                           output                          core_mem_wait,
                           output                          core_badmem_e
                           );


   assign haddr = core_mem_addr;
   assign hwrite = core_mem_en && core_mem_wen;
   assign hsize = core_mem_size;
   assign hburst = `HASTI_BURST_SINGLE;
   assign hmastlock = `HASTI_MASTER_NO_LOCK;
   assign hprot = `HASTI_NO_PROT;
   assign htrans = core_mem_en ? `HASTI_TRANS_NONSEQ : `HASTI_TRANS_IDLE;
   assign hwdata = core_mem_wdata_delayed;
   assign core_mem_rdata = hrdata;
   assign core_mem_wait = ~hready;
   assign core_badmem_e = hresp == `HASTI_RESP_ERROR;

endmodule // vscale_hasti_bridge

