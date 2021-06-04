// `include "/home/merl/github_repos/azadi/src/spi_host/rtl/spi_defines.v"
//`include "/home/zeeshan/fyp/azadi/src/spi_host/rtl/spi_defines.v"
`include "spi_defines.v"
module spi_core
(
  // tlul signals
  input         clk_i,        
  input         rst_ni,        
  input  [7:0]  addr_i,            
  input  [31:0] wdata_i,              
  output reg [31:0] rdata_o,             
  input  [3:0]  be_i,           
  input         we_i,       
  input         re_i,        
  output reg    error_o,       
  output reg    intr_rx_o,
  output reg    intr_tx_o,         
                                                     
  // SPI signals                                     
  output     [`SPI_SS_NB-1:0] ss_o,         // slave select
  output                      sclk_o,       // serial clock
  output                      sd_o,
  output     reg              sd_oe,       // master out slave in
  input                       sd_i       // master in slave out
);

                                               
  // Internal signals
  reg       [`SPI_DIVIDER_LEN-1:0] divider;          // Divider register
  reg       [`SPI_CTRL_BIT_NB-1:0] ctrl;             // Control and status register
  reg             [`SPI_SS_NB-1:0] ss;               // Slave select register
  reg                     [32-1:0] wb_dat;           // wb data out
  wire         [`SPI_MAX_CHAR-1:0] rx;               // Rx register
  wire                             rx_negedge;       // miso is sampled on negative edge
  wire                             tx_negedge;       // mosi is driven on negative edge
  wire    [`SPI_CHAR_LEN_BITS-1:0] char_len;         // char len
  wire                             go;               // go
  wire                             lsb;              // lsb first on line
  wire                             ie;               // interrupt enable
  wire                             ass;              // automatic slave select
  wire                             spi_divider_sel;  // divider register select
  wire                             spi_ctrl_sel;     // ctrl register select
  wire                             spi_tx_sel;       // tx_l register select
  wire                             spi_ss_sel;       // ss register select
  wire                             tip;              // transfer in progress
  wire                             pos_edge;         // recognize posedge of sclk
  wire                             neg_edge;         // recognize negedge of sclk
  wire                             last_bit;         // marks last character bit
  wire                             tx_en;            // enables spi transmission
  wire                             rx_en;            // enables spi reception
  
  // Address decoder
  assign spi_divider_sel = we_i & ~re_i & (addr_i[`SPI_OFS_BITS] == `SPI_DEVIDE);
  assign spi_ctrl_sel    = we_i & ~re_i & (addr_i[`SPI_OFS_BITS] == `SPI_CTRL);
  assign spi_tx_sel      = we_i & ~re_i & (addr_i[`SPI_OFS_BITS] == `SPI_TX_0) & tx_en;
  assign spi_ss_sel      = we_i & ~re_i & (addr_i[`SPI_OFS_BITS] == `SPI_SS);
  
  // Read from registers
  always @(addr_i or rx or ctrl or divider or ss)
  begin
    case (addr_i[`SPI_OFS_BITS])
      `SPI_RX_0:    wb_dat =  rx[`SPI_MAX_CHAR-1:0];
      `SPI_CTRL:    wb_dat =  ctrl;
      `SPI_DEVIDE:  wb_dat =  divider;
      `SPI_SS:      wb_dat =  ss;
      default:      wb_dat =  32'b0;
    endcase
  end
  
  // Wb data out
  always @(posedge clk_i)
  begin
    if (~rst_ni)
      rdata_o <=  32'b0;
    else
      rdata_o <=  wb_dat;
  end

  
  // Wb error
  assign error_o = 1'b0;
  
  // Interrupt
  always @(posedge clk_i)
  begin
    if (~rst_ni)
      intr_tx_o <=  1'b0;
    else if (ie && tip && last_bit && pos_edge && tx_en)
      intr_tx_o <=  1'b1;
    else 
      intr_tx_o <=  1'b0;
  end

  always @(posedge clk_i )
  begin
    if (~rst_ni)
      intr_rx_o <=  1'b0;
    else if (ie && tip && last_bit && pos_edge && rx_en)
      intr_rx_o <=  1'b1;
    else 
      intr_rx_o <=  1'b0;
  end
  
  // Divider register
  always @(posedge clk_i)
  begin
    if (~rst_ni)
        divider <=  {`SPI_DIVIDER_LEN{1'b0}};
    else if (spi_divider_sel && we_i && !tip)
      begin
        if (be_i[0])
          divider[7:0] <=  wdata_i[7:0];
        if (be_i[1])
          divider[`SPI_DIVIDER_LEN-1:8] <=  wdata_i[`SPI_DIVIDER_LEN-1:8];
      end
  end
  
  // Ctrl register
  always @(posedge clk_i)
  begin
    if (~rst_ni)
      ctrl <=  {`SPI_CTRL_BIT_NB{1'b0}};
    else if(spi_ctrl_sel && we_i && !tip)
      begin
        if (be_i[0])
          ctrl[7:0] <=  wdata_i[7:0] | {7'b0, ctrl[0]};
        if (be_i[1])
          ctrl[`SPI_CTRL_BIT_NB-1:8] <=  wdata_i[`SPI_CTRL_BIT_NB-1:8];
      end
    else if(tip && last_bit && pos_edge)
      ctrl[`SPI_CTRL_GO] <=  1'b0;
  end
  
  assign rx_negedge = ctrl[`SPI_CTRL_RX_NEGEDGE];
  assign tx_negedge = ctrl[`SPI_CTRL_TX_NEGEDGE];
  assign go         = ctrl[`SPI_CTRL_GO];
  assign char_len   = ctrl[`SPI_CTRL_CHAR_LEN];
  assign lsb        = ctrl[`SPI_CTRL_LSB];
  assign ie         = ctrl[`SPI_CTRL_IE];
  assign ass        = ctrl[`SPI_CTRL_ASS];
  assign rx_en      = ctrl[`SPI_RX_SEL];
  assign tx_en      = ctrl[`SPI_TX_SEL];
  
  always @(posedge clk_i or negedge rst_ni) begin
    if(~rst_ni) begin
        sd_oe <= 1'b0;
    end else if (tx_en & !rx_en) begin
        sd_oe <= 1'b1;
    end else begin
        sd_oe <= 1'b0;
    end 
  end
  // Slave select register
  always @(posedge clk_i)
  begin
    if (~rst_ni)
      ss <=  {`SPI_SS_NB{1'b0}};
    else if(spi_ss_sel && we_i && !tip)
      begin
        if (be_i[0])
          ss <=  wdata_i[`SPI_SS_NB-1:0];
      end
  end
  
  assign ss_o = ~((ss & {`SPI_SS_NB{tip & ass}}) | (ss & {`SPI_SS_NB{!ass}}));
  
  spi_clgen clgen (
    .clk_i       (clk_i), 
    .rst_ni      (rst_ni), 
    .go          (go), 
    .enable      (tip), 
    .last_clk    (last_bit),
    .divider     (divider), 
    .clk_out     (sclk_o), 
    .pos_edge    (pos_edge), 
    .neg_edge    (neg_edge)
    );
  
  spi_shift shift (
    .clk_i        (clk_i), 
    .rst_ni       (rst_ni), 
    .len          (char_len[`SPI_CHAR_LEN_BITS-1:0]),
    .latch        (spi_tx_sel & we_i), 
    .byte_sel     (be_i), 
    .lsb          (lsb), 
    .go           (go), 
    .pos_edge     (pos_edge), 
    .neg_edge     (neg_edge), 
    .rx_negedge   (rx_negedge), 
    .tx_negedge   (tx_negedge),
    .tip          (tip), 
    .last         (last_bit), 
    .p_in         (wdata_i), 
    .p_out        (rx), 
    .s_clk        (sclk_o), 
    .s_in         (sd_i), 
    .s_out        (sd_o),
    .rx_en        (rx_en) 
    );
endmodule
  
