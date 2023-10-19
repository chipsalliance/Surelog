


module UART(
    input clk
);

 

endmodule


module UART_assertions (
    input clk
    
);


endmodule

      
      bind UART UART_assertions uut(.state(clk));