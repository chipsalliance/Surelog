module TestFunction (
   output logic O1, O2, O3, O4,
    input wire logic[2:0] sw , sw2);
    /*
    always_comb begin
    if(sw[0])
        O1 = 1'b1;
    else
        O1 = 1'b0;
    
    if(sw[1])
        O2 = 1'b1;
    else      
        O2 = 1'b0;
 
    if(sw[2])
        O3 = 1'b1;
    else
        O3 = 1'b0;

    end
    */ 
endmodule // TestFunction
