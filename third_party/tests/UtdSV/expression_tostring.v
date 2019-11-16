
`define NUMBER 65
    
module dummy();
    
    assign d = `NUMBER - 1;

    assign Z = 32'b0010101;
    
    assign a = !b;

    assign cc_mvbr_d = ~(~op_d[1] & ~op_d[0] & op3_d[4] & op3_d[3] |
 			             op_d[1] & ~op_d[0] & op3_d[5] & ~op3_d[4] &
 			            op3_d[3] & op3_d[2] & op3_d[1] & op3_d[0] | 
 			             op_d[1] & ~op_d[0] & op3_d[5] & op3_d[4] &
 			           ~op3_d[3] & op3_d[2] & ~op3_d[1] & op3_d[0] &
 			             dtu_dcl_opf2_d);                           
    

endmodule
