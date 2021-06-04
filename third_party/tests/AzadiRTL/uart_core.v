
module uart_core (
    input  clk_i,
    input  rst_ni,
    
    input  ren,
    input  we,
    input  [31:0] wdata,
    output [31:0] rdata,
    input  [7:0]  addr,    
    output tx_o,
    input  rx_i,
    
    output intr_tx
);
    
    localparam ADDR_CTRL = 0;
    localparam ADDR_TX   = 4;
    localparam ADDR_RX   = 8;
    
    reg [20:0] control;
    reg [7:0]  tx;
    wire [7:0] rx;
    wire       rx_status;
    
    always @(posedge clk_i) begin
        if(~rst_ni) begin
            control <= 0;
            tx      <= 0;
        end else begin
          if(~ren & we) begin
            if(addr == ADDR_CTRL) begin
                control[1:0] <= wdata[1:0];
                control[19:3]<= wdata[19:3];
                control[2]   <= rx_status;
            end else if (addr == ADDR_TX) begin
                tx  <= wdata[7:0];
            end else if (addr == ADDR_RX) begin
            end else begin
                control <= 0;
                tx      <= 0;
            end
        end 
    end     
  end
    
    
uart_tx u_tx (
   .clk_i       (clk_i),
   .rst_ni      (rst_ni),
   .tx_en       (control[0]),
   .i_TX_Byte   (tx), 
   .CLKS_PER_BIT(control[19:3]),
       //output      o_TX_Active,
   .o_TX_Serial (tx_o),
   .o_TX_Done   (intr_tx)
);
    
uart_rx u_rx(
  .clk_i        (clk_i),
  .rst_ni       (rst_ni),
  .i_RX_Serial  (rx_i),
  .o_RX_DV      (rx_status),
  .rx_en        (control[1]),
  .CLKS_PER_BIT (control[19:3]),
  .o_RX_Byte    (rx)
);
  
 assign rdata = (addr == 0)? control: (addr == 8)? rx : 0;   
      
   
endmodule