module iNToRawFN#(parameter intWidth = 1) (signedIn, sExp);
    localparam expWidth = clog2(intWidth) + 1;
    wire [(expWidth - 2):0] adjustedNormDist;
endmodule

module iNToRawFN3#(parameter intWidth = 1, parameter intWidth2 = 1) (signedIn, sExp);
    localparam expWidth = clog2(intWidth) + 1;
    localparam expWidth2 = clog2(intWidth2) + 1;
    wire [(expWidth - 2):0] adjustedNormDist;
    wire [(expWidth2 - 2):0] adjustedNormDist2;
endmodule


primitive BUFG ( O, I );
   output O;
   input I;
   table
      0 : 0 ;
      1 : 1 ;
   endtable
endprimitive

module iNToRecFN#( parameter intWidth = 64, parameter intWidth2 = 64 ) ( );
 iNToRawFN#(intWidth) iNToRawFN(signedIn, sExp);
 iNToRawFN3#(intWidth, intWidth2) iNToRawFN3(signedIn, sExp);

BUFG #5 bg(out, in);

endmodule // iNToRecFN

