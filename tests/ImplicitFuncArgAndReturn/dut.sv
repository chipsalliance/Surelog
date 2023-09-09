

module sub();
   parameter int M_SECURE = 1;
   
endmodule // sub


module ScratchPad (
 
);
   parameter M00_SECURE = 1'b0;

   
function w_1(input val);
    w_1 = val;
endfunction

  // parameter D = w_1(M00_SECURE);
   //sub #( .M_SECURE( w_1(M00_SECURE) )) m1();
   sub #( .M_SECURE({ w_1(M00_SECURE) })) m1();
   

endmodule
