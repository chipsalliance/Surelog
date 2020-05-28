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

