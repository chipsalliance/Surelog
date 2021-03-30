package gpio_reg_pkg;                                                                                    
  typedef struct packed {                                                                                
    logic [31:0] d;                        
    logic        de;                                
  } gpio_hw2reg_tt;                      
                                                                                                         
  typedef struct packed {                           
    gpio_hw2reg_tt data_in;              
  } gpio_hw2reg_t;                      
                                                                                                         
endpackage                                                                                               
                                                                                                         
module dut();                                                                                            
                                                                                                         
import gpio_reg_pkg::*;                                                                                  
gpio_hw2reg_t hw2reg;                                                                                    
assign hw2reg.data_in.de = 1'b1;                                                                         
                                                                                                         
endmodule
