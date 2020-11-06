interface MyInterface;
   logic my_logic;
   modport MyModPort
   (
      output      my_logic
   );
endinterface

module range_itf_port (
    MyInterface.MyModPort my_port1[1:0],
    input logic my_port2[1:0]
);
endmodule
