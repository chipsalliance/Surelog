// `include "/home/merl/github_repos/azadi/src/spi_host/rtl/spi_defines.v"
//`include "/home/zeeshan/fyp/azadi/src/spi_host/rtl/spi_defines.v"
`include "spi_defines.v"
module spi_top(

  input clk_i,
  input rst_ni,

  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // SPI signals                  
  output     intr_rx_o,
  output     intr_tx_o,                   
  output     [`SPI_SS_NB-1:0] ss_o,        
  output                      sclk_o,      
  output                      sd_o,
  output                      sd_oe,       
  input                       sd_i      

);

localparam int AW = 8;
localparam int DW = 32;

logic         re;
logic         we;
logic [7:0]   addr;
logic [31:0]  wdata;
logic [3:0]   be;
logic [31:0]  rdata;
logic         err;

spi_core spi_host(
  // tlul signals
  .clk_i,        
  .rst_ni,        
  .addr_i      (addr),            
  .wdata_i     (wdata),              
  .rdata_o     (rdata),             
  .be_i        (be),           
  .we_i        (we),       
  .re_i        (re),        
  .error_o     (err),

  .intr_rx_o   (intr_rx_o),
  .intr_tx_o   (intr_tx_o),         
                                                     
  // SPI signals                                     
  .ss_o        (ss_o),         // slave select
  .sclk_o      (sclk_o),       // serial clock
  .sd_o        (sd_o),       // master out slave in
  .sd_oe       (sd_oe),
  .sd_i        (sd_i)     // master in slave out
);


tlul_adapter_reg #(
  .RegAw(AW),
  .RegDw(DW)
) u_reg_if (
  .clk_i,
  .rst_ni,

  .tl_i    (tl_i),
  .tl_o    (tl_o),

  .we_o    (we),
  .re_o    (re),
  .addr_o  (addr),
  .wdata_o (wdata),
  .be_o    (be),
  .rdata_i (rdata),
  .error_i (err)
);

endmodule