module iNToRawFN#(parameter intWidth = 1) (signedIn, sExp);
    localparam expWidth = clog2(intWidth) + 1;
    wire [(expWidth - 2):0] adjustedNormDist;
endmodule


primitive BUFG ( O, I );
   output O;
   input I;
   table
      0 : 0 ;
      1 : 1 ;
   endtable
endprimitive


module iNToRecFN#( parameter intWidth = 64 ) ( );

 iNToRawFN#(intWidth) iNToRawFN(signedIn, sExp);

 BUFG #5 bg(out, in);

endmodule
