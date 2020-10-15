/* Test attribute on package */
(* myPackageAttribute1 *)
package myPackage;
endpackage

/* Test attribute on primitive */
(* attribute_udp *) primitive multiplexer (mux, control, dataA, dataB);
output mux;
input control, dataA, dataB;
table
// control dataA dataB mux
0 1 0 : 1 ;
0 1 1 : 1 ;
0 1 x : 1 ;
0 0 0 : 0 ;
0 0 1 : 0 ;
0 0 x : 0 ;
1 0 1 : 1 ;
1 1 1 : 1 ;
1 x 1 : 1 ;
1 0 0 : 0 ;
1 1 0 : 0 ;
1 x 0 : 0 ;
x 0 0 : 0 ;
x 1 1 : 1 ;
endtable
endprimitive


/* Test attribute on module */
(* mymoduleTop *)
module top;

  (* mymoduleTop2 *)
  module top2;
  endmodule
  

endmodule

/* Test attribute on class */
(* class_attribute *) class toto;


  (* class_attribute2*) class tata;
  endclass


endclass;

/* Test attribute on interface */
(* test_interface *) interface itf;
 
  (* test_interface2 *) interface itf2;
  endinterface;

endinterface

