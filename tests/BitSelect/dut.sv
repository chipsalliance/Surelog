module alert_sender                            
#(                                                                                                       
  parameter bit AsyncOn = 1'b0                      
) ();                                               
endmodule                               
module dut();                                                                                            
parameter int                   NumAlerts = 3;                                                           
parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}};          
parameter res =  AlertAsyncOn[0];                             
for (genvar i = 0; i < NumAlerts; i++) begin: gen_alert_tx                                               
  alert_sender #(                                                                                   
    .AsyncOn(AlertAsyncOn[i])                                                                            
  ) i_alert_sender ();                                                                              
end                                                                                                                                                                                                
endmodule
