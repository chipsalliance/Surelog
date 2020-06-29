/*
:name: interface
:description: interface test
:tags: 25.3
*/

interface test_bus;
  logic test_pad;
endinterface: test_bus

module sub(test_bus iface);
endmodule

module top;
   test_bus iface;
   sub sub (.iface);
endmodule
