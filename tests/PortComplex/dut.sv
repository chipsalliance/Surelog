package pr_pkg;                             
  typedef struct packed {      
    logic alert_p;                                                                                
    logic alert_n;                       
  } alert_tx_t;                                                                             
                                                                                        
endpackage         

module dut( 
output pr_pkg::alert_tx_t [2:0] alert_tx_o                                                     
); 

endmodule
