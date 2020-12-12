interface abc_if #(int NO_Input=3);
 
  logic [NO_Input-1 :0 ] xyz_o;   
  logic [NO_Input-1 :0 ] clk_i;
 
   for(genvar i=0;i<NO_Input;i++)begin : block
      clocking abc_cb @(posedge clk_i[i]);
        // output xyz_drive = xyz_o[i];  << Syntax error here to be investigated!
   endclocking 
   end : block
// then you can drive 
   //  block[0].abc_cb.xyz_drive <= '1; // drives xyz_o[0]  << Syntax error here to be investigated!
endinterface


module top ();
  abc_if intf();

endmodule


interface pins_if #( parameter int Width = 1 ) (
  inout [Width-1:0] pins
);
  logic [Width-1:0] pins_o;       // value to be driven out
  // make connections
  generate
    for (genvar i = 0; i < Width; i++) begin : each_pin_intf   
      assign pins[i] = pins_oe[i] ? pins_o[i] : 1'bz;
    end
  endgenerate
endinterface

module top2 #( parameter int Width = 2 ) (inout [Width-1:0] pins);
pins_if #(.Width(Width)) intf  (pins);

  generate
    for (genvar i = 0; i < Width; i++) begin : each_pin 
      assign pins[i] = pins_oe[i] ? pins_o[i] : 1'bz;
    end
  endgenerate

endmodule
