`celldefine
module FAKELIB_NAND2(output OUT, input IN0,IN1 );
  assign OUT = ~(IN0 & IN1);
endmodule
module FAKELIB_NAND4(output OUT, input IN0,IN1,IN2,IN3 );
  assign OUT = ~(IN0 & IN1 & IN2 & IN3);
endmodule
module FAKELIB_NOR2(output OUT, input IN0,IN1 );
  assign OUT = ~(IN1 | IN0);
endmodule
module FAKELIB_INV(output OUT, input IN );
  assign OUT = ~IN;
endmodule
module FAKELIB_BUF(output OUT, input IN );
  assign OUT = IN;
endmodule
module FAKELIB_BUF_BIGLOAD(output OUT, input IN );
  assign OUT = IN;
endmodule
module FAKELIB_DFF(output reg Q, input CLK, RST_N, SET_N, D );
  FAKELIB_DFF_PRIMITIVE dff(Q, CLK, RST_N, SET_N, D);
endmodule
// ... more standard cells ...
`endcelldefine
primitive FAKELIB_DFF_PRIMITIVE(output reg Q, input CLK, RST_N, SET_N, D  );
  table
   // CLK RST_N SET_N D : Q(state) : Q(next)
       ?    0     ?   ? : ? : 0;
       ?    1     0   ? : ? : 1;
       p    1     1   0 : ? : 0;
       p    1     1   1 : ? : 1;
      (?0)  1     1   ? : ? : -;
       ?    1     1   * : ? : -;
  endtable
endprimitive
