module prim_subreg(                                 
input logic test                                                                                  
);                                                                                                       
                                                                                                         
endmodule                                                                                                
                                                                                                         
module dut();                                                                                            
                                                                                                         
prim_subreg s(.test({24 {1'sb0}}));                                                                       
endmodule

