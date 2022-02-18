module GOOD();

endmodule

module dut();

parameter test = 4'b0011;

for (genvar k = 0; k < 4; k++) begin
  if (test[k]) begin
    MOD m ();
    if (k == 0 || k == 1) begin
       GOOD good();      
    end else begin
       BAD bad();
    end 
     
  end
end

endmodule // dut
