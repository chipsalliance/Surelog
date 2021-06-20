
interface REG_BUS #(
  /// The width of the address.
  parameter int ADDR_WIDTH = -1
)(
  input logic clk_i
);

  logic [ADDR_WIDTH-1:0]   addr;
 
  modport out (output addr);

endinterface

module apb_to_reg (
  REG_BUS.out  reg_o
);
 
endmodule

module peripherals ();
   
   REG_BUS #(
        .ADDR_WIDTH ( 32 )
    ) reg_bus (clk_i);

apb_to_reg i_apb_to_reg (.reg_o( reg_bus));

endmodule 


module testharness();

  peripherals  i_peripherals ();

endmodule
