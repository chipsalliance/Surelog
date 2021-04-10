module dut (b);                                                                                          
        wire a = 0;      
        output reg b = 0;                                                                        
        always @* begin                                                                                  
                if(a) b = 1;                                                                     
        end   
   assign c = a;
                                                                                           
endmodule
