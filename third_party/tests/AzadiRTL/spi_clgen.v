// `include "/home/merl/github_repos/azadi/src/spi_host/rtl/spi_defines.v"
`include "spi_defines.v"

module spi_clgen (
  input                            clk_i,   // input clock (system clock)
  input                            rst_ni,      // reset
  input                            enable,   // clock enable
  input                            go,       // start transfer
  input                            last_clk, // last clock
  input     [`SPI_DIVIDER_LEN-1:0] divider,  // clock divider (output clock is divided by this value)
  output    reg                    clk_out,  // output clock
  output    reg                    pos_edge, // pulse marking positive edge of clk_out
  output    reg                    neg_edge // pulse marking negative edge of clk_out

); 
                            
  //reg                              clk_out;
  //reg                              pos_edge;
  //reg                              neg_edge;
                            
  reg       [`SPI_DIVIDER_LEN-1:0] cnt;      // clock counter 
  wire                             cnt_zero; // conter is equal to zero
  wire                             cnt_one;  // conter is equal to one
  
  
  assign cnt_zero = cnt == {`SPI_DIVIDER_LEN{1'b0}};
  assign cnt_one  = cnt == {{`SPI_DIVIDER_LEN-1{1'b0}}, 1'b1};
  
  // Counter counts half period
  always @(posedge clk_i or negedge rst_ni)
  begin
    if(~rst_ni)
      cnt <=  {`SPI_DIVIDER_LEN{1'b1}};
    else
      begin
        if(!enable || cnt_zero)
          cnt <=  divider;
        else
          cnt <=  cnt - {{`SPI_DIVIDER_LEN-1{1'b0}}, 1'b1};
      end
  end
  
  // clk_out is asserted every other half period
  always @(posedge clk_i or negedge rst_ni)
  begin
    if(~rst_ni)
      clk_out <=  1'b0;
    else
      clk_out <=  (enable && cnt_zero && (!last_clk || clk_out)) ? ~clk_out : clk_out;
  end
   
  // Pos and neg edge signals
  always @(posedge clk_i or negedge rst_ni)
  begin
    if(~rst_ni)
      begin
        pos_edge  <=  1'b0;
        neg_edge  <=  1'b0;
      end
    else
      begin
        pos_edge  <=  (enable && !clk_out && cnt_one) || (!(|divider) && clk_out) || (!(|divider) && go && !enable);
        neg_edge  <=  (enable && clk_out && cnt_one) || (!(|divider) && !clk_out && enable);
      end
  end
endmodule
 
