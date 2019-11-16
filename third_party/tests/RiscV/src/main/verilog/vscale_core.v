`include "vscale_hasti_constants.vh"
`include "vscale_ctrl_constants.vh"
`include "vscale_csr_addr_map.vh"
`include "vscale_platform_constants.vh"

module vscale_core(
                   input 			   clk,
		   input [`N_EXT_INTS-1:0] 	   ext_interrupts, 
                   output [`HASTI_ADDR_WIDTH-1:0]  imem_haddr,
                   output 			   imem_hwrite,
                   output [`HASTI_SIZE_WIDTH-1:0]  imem_hsize,
                   output [`HASTI_BURST_WIDTH-1:0] imem_hburst,
                   output 			   imem_hmastlock,
                   output [`HASTI_PROT_WIDTH-1:0]  imem_hprot,
                   output [`HASTI_TRANS_WIDTH-1:0] imem_htrans,
                   output [`HASTI_BUS_WIDTH-1:0]   imem_hwdata,
                   input [`HASTI_BUS_WIDTH-1:0]    imem_hrdata,
                   input 			   imem_hready,
                   input [`HASTI_RESP_WIDTH-1:0]   imem_hresp,
                   output [`HASTI_ADDR_WIDTH-1:0]  dmem_haddr,
                   output 			   dmem_hwrite,
                   output [`HASTI_SIZE_WIDTH-1:0]  dmem_hsize,
                   output [`HASTI_BURST_WIDTH-1:0] dmem_hburst,
                   output 			   dmem_hmastlock,
                   output [`HASTI_PROT_WIDTH-1:0]  dmem_hprot,
                   output [`HASTI_TRANS_WIDTH-1:0] dmem_htrans,
                   output [`HASTI_BUS_WIDTH-1:0]   dmem_hwdata,
                   input [`HASTI_BUS_WIDTH-1:0]    dmem_hrdata,
                   input 			   dmem_hready,
                   input [`HASTI_RESP_WIDTH-1:0]   dmem_hresp,
                   input 			   htif_reset,
                   input 			   htif_id,
                   input 			   htif_pcr_req_valid,
                   output 			   htif_pcr_req_ready,
                   input 			   htif_pcr_req_rw,
                   input [`CSR_ADDR_WIDTH-1:0] 	   htif_pcr_req_addr,
                   input [`HTIF_PCR_WIDTH-1:0] 	   htif_pcr_req_data,
                   output 			   htif_pcr_resp_valid,
                   input 			   htif_pcr_resp_ready,
                   output [`HTIF_PCR_WIDTH-1:0]    htif_pcr_resp_data,
                   input 			   htif_ipi_req_ready,
                   output 			   htif_ipi_req_valid,
                   output 			   htif_ipi_req_data,
                   output 			   htif_ipi_resp_ready,
                   input 			   htif_ipi_resp_valid,
                   input 			   htif_ipi_resp_data,
                   output 			   htif_debug_stats_pcr
                   );

   wire                                            imem_wait;
   wire [`HASTI_ADDR_WIDTH-1:0]                    imem_addr;
   wire [`HASTI_BUS_WIDTH-1:0]                     imem_rdata;
   wire                                            imem_badmem_e;
   wire                                            dmem_wait;
   wire                                            dmem_en;
   wire                                            dmem_wen;
   wire [`HASTI_SIZE_WIDTH-1:0]                    dmem_size;
   wire [`HASTI_ADDR_WIDTH-1:0]                    dmem_addr;
   wire [`HASTI_BUS_WIDTH-1:0]                     dmem_wdata_delayed;
   wire [`HASTI_BUS_WIDTH-1:0]                     dmem_rdata;
   wire                                            dmem_badmem_e;

   assign htif_ipi_req_valid = 1'b0;
   assign htif_ipi_req_data = 1'b0;
   assign htif_ipi_resp_ready = 1'b1;
   assign htif_debug_stats_pcr = 1'b0;

   vscale_hasti_bridge imem_bridge(
                                   .haddr(imem_haddr),
                                   .hwrite(imem_hwrite),
                                   .hsize(imem_hsize),
                                   .hburst(imem_hburst),
                                   .hmastlock(imem_hmastlock),
                                   .hprot(imem_hprot),
                                   .htrans(imem_htrans),
                                   .hwdata(imem_hwdata),
                                   .hrdata(imem_hrdata),
                                   .hready(imem_hready),
                                   .hresp(imem_hresp),
                                   .core_mem_en(1'b1),
                                   .core_mem_wen(1'b0),
                                   .core_mem_size(`HASTI_SIZE_WORD),
                                   .core_mem_addr(imem_addr),
                                   .core_mem_wdata_delayed(32'b0),
                                   .core_mem_rdata(imem_rdata),
                                   .core_mem_wait(imem_wait),
                                   .core_badmem_e(imem_badmem_e)
                                   );

   vscale_hasti_bridge dmem_bridge(
                                   .haddr(dmem_haddr),
                                   .hwrite(dmem_hwrite),
                                   .hsize(dmem_hsize),
                                   .hburst(dmem_hburst),
                                   .hmastlock(dmem_hmastlock),
                                   .hprot(dmem_hprot),
                                   .htrans(dmem_htrans),
                                   .hwdata(dmem_hwdata),
                                   .hrdata(dmem_hrdata),
                                   .hready(dmem_hready),
                                   .hresp(dmem_hresp),
                                   .core_mem_en(dmem_en),
                                   .core_mem_wen(dmem_wen),
                                   .core_mem_size(dmem_size),
                                   .core_mem_addr(dmem_addr),
                                   .core_mem_wdata_delayed(dmem_wdata_delayed),
                                   .core_mem_rdata(dmem_rdata),
                                   .core_mem_wait(dmem_wait),
                                   .core_badmem_e(dmem_badmem_e)
                                   );


   vscale_pipeline pipeline(
                            .clk(clk),
			    .ext_interrupts(ext_interrupts),
                            .reset(htif_reset),
                            .imem_wait(imem_wait),
                            .imem_addr(imem_addr),
                            .imem_rdata(imem_rdata),
                            .imem_badmem_e(imem_badmem_e),
                            .dmem_wait(dmem_wait),
                            .dmem_en(dmem_en),
                            .dmem_wen(dmem_wen),
                            .dmem_size(dmem_size),
                            .dmem_addr(dmem_addr),
                            .dmem_wdata_delayed(dmem_wdata_delayed),
                            .dmem_rdata(dmem_rdata),
                            .dmem_badmem_e(dmem_badmem_e),
                            .htif_reset(htif_reset),
                            .htif_pcr_req_valid(htif_pcr_req_valid),
                            .htif_pcr_req_ready(htif_pcr_req_ready),
                            .htif_pcr_req_rw(htif_pcr_req_rw),
                            .htif_pcr_req_addr(htif_pcr_req_addr),
                            .htif_pcr_req_data(htif_pcr_req_data),
                            .htif_pcr_resp_valid(htif_pcr_resp_valid),
                            .htif_pcr_resp_ready(htif_pcr_resp_ready),
                            .htif_pcr_resp_data(htif_pcr_resp_data)
                            );

endmodule // vscale_core

