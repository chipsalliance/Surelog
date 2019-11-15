module top(input clk);
  MyInterface MyInterfaceInstance();
endmodule

interface MyInterface();
  logic not_an_empty_interface;
endinterface
