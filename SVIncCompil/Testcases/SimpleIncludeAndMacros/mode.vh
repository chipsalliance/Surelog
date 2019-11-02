
/*
   mode.vh
*/

`define BLOB \
   `ifdef N \
     `ifdef M1 \
      reg blob_m1; \
     `elsif M2 \
      reg blob_m2; \
     `else \
      reg blob_e; \
      `include "wire.vh" \
     `timescale 10ns/10ps \
      $display("Internal error: null handle at %s, line %d.",`__FILE__, `__LINE__); \
     `endif \
   `endif


`define macro_with_args(A, B) \
     reg A, B; \
     assign A = B;

`define D(x,y) initial $display("start", x , y, "end");
`D( "msg1" , "msg2" )
// expands to 'initial $display("start", "msg1" , "msg2", "end");'
`D( " msg1", )
// expands to 'initial $display("start", " msg1" , , "end");'
`D(, "msg2 ")
// expands to 'initial $display("start", , "msg2 ", "end");'
`D(,)
// expands to 'initial $display("start", , , "end");'
`D( , )
// expands to 'initial $display("start", , , "end");'
`D("msg1")
// illegal, only one argument
`D()
// illegal, only one empty argument
`D(,,)
// illegal, more actual than formal arguments
`define MACRO1(a=5,b="B",c) $display(a,,b,,c);
`MACRO1 ( , 2, 3 ) // argument a omitted, replaced by default
 // expands to '$display(5,,2,,3);'
`MACRO1 ( 1 , , 3 ) // argument b omitted, replaced by default
 // expands to '$display(1,,"B",,3);'
`MACRO1 ( , 2, ) // argument c omitted, replaced by nothing
 // expands to '$display(5,,2,,);'
`MACRO1 ( 1 ) // ILLEGAL: b and c omitted, no default for c
`define MACRO2(a=5, b, c="C") $display(a,,b,,c);
`MACRO2 (1, , 3) // argument b omitted, replaced by nothing
 // expands to '$display(1,,,,3);'
`MACRO2 (, 2, ) // a and c omitted, replaced by defaults
 // expands to '$display(5,,2,,"C");'
`MACRO2 (, 2) // a and c omitted, replaced by defaults
 // expands to '$display(5,,2,,"C");'
`define MACRO3(a=5, b=0, c="C") $display(a,,b,,c);
`MACRO3 ( 1 ) // b and c omitted, replaced by defaults
 // expands to '$display(1,,0,,"C");'
`MACRO3 ( ) // all arguments replaced by defaults
 // expands to '$display(5,,0,,"C");'
`MACRO3 // ILLEGAL: parentheses required
   