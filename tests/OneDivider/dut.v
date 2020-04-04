module dut(input logic rstn,
           input logic clk,
           output reg div);
 
always @ (posedge clk or negedge rstn) 
       if (!rstn)
          div <= 0;
       else
          div <= !div;
endmodule
 
