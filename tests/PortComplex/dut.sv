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

package dm;                                                                                              
typedef struct packed {                                                                                  
  logic [31:24] zero1;                     
  logic [23:20] nscratch;                           
  logic [19:17] zero0;                              
  logic         dataaccess;                                                                              
  logic [15:12] datasize;                           
  logic [11:0]  dataaddr;                           
} hartinfo_t;                           
endpackage                                                                                               
                                                                                                         
module dut2 #(                                                                                            
parameter int unsigned        NrHarts          = 1                                                       
)                                                                                                        
(                                                                                                        
  input dm::hartinfo_t [NrHarts-1:0]       hartinfo_i,                                                   
  input dm::hartinfo_t                     hart_info_i_without_range                                     
);                                                                                                       
endmodule
