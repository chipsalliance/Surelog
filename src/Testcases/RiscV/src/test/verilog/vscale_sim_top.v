`include "vscale_ctrl_constants.vh"
`include "vscale_csr_addr_map.vh"
`include "vscale_hasti_constants.vh"

module vscale_sim_top(
                      input                        clk,
                      input                        reset,
                      input                        htif_pcr_req_valid,
                      output                       htif_pcr_req_ready,
                      input                        htif_pcr_req_rw,
                      input [`CSR_ADDR_WIDTH-1:0]  htif_pcr_req_addr,
                      input [`HTIF_PCR_WIDTH-1:0]  htif_pcr_req_data,
                      output                       htif_pcr_resp_valid,
                      input                        htif_pcr_resp_ready,
                      output [`HTIF_PCR_WIDTH-1:0] htif_pcr_resp_data
                      );

   wire                                            resetn;

   wire [`HASTI_ADDR_WIDTH-1:0]                    imem_haddr;
   wire                                            imem_hwrite;
   wire [`HASTI_SIZE_WIDTH-1:0]                    imem_hsize;
   wire [`HASTI_BURST_WIDTH-1:0]                   imem_hburst;
   wire                                            imem_hmastlock;
   wire [`HASTI_PROT_WIDTH-1:0]                    imem_hprot;
   wire [`HASTI_TRANS_WIDTH-1:0]                   imem_htrans;
   wire [`HASTI_BUS_WIDTH-1:0]                     imem_hwdata;
   wire [`HASTI_BUS_WIDTH-1:0]                     imem_hrdata;
   wire                                            imem_hready;
   wire [`HASTI_RESP_WIDTH-1:0]                    imem_hresp;

   wire [`HASTI_ADDR_WIDTH-1:0]                    dmem_haddr;
   wire                                            dmem_hwrite;
   wire [`HASTI_SIZE_WIDTH-1:0]                    dmem_hsize;
   wire [`HASTI_BURST_WIDTH-1:0]                   dmem_hburst;
   wire                                            dmem_hmastlock;
   wire [`HASTI_PROT_WIDTH-1:0]                    dmem_hprot;
   wire [`HASTI_TRANS_WIDTH-1:0]                   dmem_htrans;
   wire [`HASTI_BUS_WIDTH-1:0]                     dmem_hwdata;
   wire [`HASTI_BUS_WIDTH-1:0]                     dmem_hrdata;
   wire                                            dmem_hready;
   wire [`HASTI_RESP_WIDTH-1:0]                    dmem_hresp;

   wire                                            htif_reset;

   wire                                            htif_ipi_req_ready = 1'b0;
   wire                                            htif_ipi_req_valid;
   wire                                            htif_ipi_req_data;
   wire                                            htif_ipi_resp_ready;
   wire                                            htif_ipi_resp_valid = 1'b0;
   wire                                            htif_ipi_resp_data = 1'b0;
   wire                                            htif_debug_stats_pcr;
   
   assign resetn = ~reset;
   assign htif_reset = reset;

   vscale_core vscale(
                      .clk(clk),
		      .ext_interrupts(0),
                      .imem_haddr(imem_haddr),
                      .imem_hwrite(imem_hwrite),
                      .imem_hsize(imem_hsize),
                      .imem_hburst(imem_hburst),
                      .imem_hmastlock(imem_hmastlock),
                      .imem_hprot(imem_hprot),
                      .imem_htrans(imem_htrans),
                      .imem_hwdata(imem_hwdata),
                      .imem_hrdata(imem_hrdata),
                      .imem_hready(imem_hready),
                      .imem_hresp(imem_hresp),
                      .dmem_haddr(dmem_haddr),
                      .dmem_hwrite(dmem_hwrite),
                      .dmem_hsize(dmem_hsize),
                      .dmem_hburst(dmem_hburst),
                      .dmem_hmastlock(dmem_hmastlock),
                      .dmem_hprot(dmem_hprot),
                      .dmem_htrans(dmem_htrans),
                      .dmem_hwdata(dmem_hwdata),
                      .dmem_hrdata(dmem_hrdata),
                      .dmem_hready(dmem_hready),
                      .dmem_hresp(dmem_hresp),
                      .htif_reset(htif_reset),
                      .htif_id(1'b0),
                      .htif_pcr_req_valid(htif_pcr_req_valid),
                      .htif_pcr_req_ready(htif_pcr_req_ready),
                      .htif_pcr_req_rw(htif_pcr_req_rw),
                      .htif_pcr_req_addr(htif_pcr_req_addr),
                      .htif_pcr_req_data(htif_pcr_req_data),
                      .htif_pcr_resp_valid(htif_pcr_resp_valid),
                      .htif_pcr_resp_ready(htif_pcr_resp_ready),
                      .htif_pcr_resp_data(htif_pcr_resp_data),
                      .htif_ipi_req_ready(htif_ipi_req_ready),
                      .htif_ipi_req_valid(htif_ipi_req_valid),
                      .htif_ipi_req_data(htif_ipi_req_data),
                      .htif_ipi_resp_ready(htif_ipi_resp_ready),
                      .htif_ipi_resp_valid(htif_ipi_resp_valid),
                      .htif_ipi_resp_data(htif_ipi_resp_data),
                      .htif_debug_stats_pcr(htif_debug_stats_pcr)
                      );

   vscale_dp_hasti_sram hasti_mem(
                                  .hclk(clk),
                                  .hresetn(resetn),
                                  .p1_haddr(imem_haddr),
                                  .p1_hwrite(imem_hwrite),
                                  .p1_hsize(imem_hsize),
                                  .p1_hburst(imem_hburst),
                                  .p1_hmastlock(imem_hmastlock),
                                  .p1_hprot(imem_hprot),
                                  .p1_htrans(imem_htrans),
                                  .p1_hwdata(imem_hwdata),
                                  .p1_hrdata(imem_hrdata),
                                  .p1_hready(imem_hready),
                                  .p1_hresp(imem_hresp),
                                  .p0_haddr(dmem_haddr),
                                  .p0_hwrite(dmem_hwrite),
                                  .p0_hsize(dmem_hsize),
                                  .p0_hburst(dmem_hburst),
                                  .p0_hmastlock(dmem_hmastlock),
                                  .p0_hprot(dmem_hprot),
                                  .p0_htrans(dmem_htrans),
                                  .p0_hwdata(dmem_hwdata),
                                  .p0_hrdata(dmem_hrdata),
                                  .p0_hready(dmem_hready),
                                  .p0_hresp(dmem_hresp)
                                  );

endmodule // vscale_sim_top
