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



interface mem_if (input wire clk);

  modport  system (input clk);
  modport  memory (output clk);
 
endinterface


module memory_ctrl1 (mem_if sif1, mem_if.system sif2);


endmodule



interface ConnectTB  (input wire [1:0] con_i) ;
endinterface

module middle (ConnectTB conn1 [1:0]);
endmodule


module range_itf_port2 (
    MyInterface.MyModPort my_port1,
    MyInterface.MyModPort my_port2[1:0],
    MyInterface  my_port3,
    MyInterface  my_port4[1:0]
		       
);
endmodule

