localparam              AWIDTH                       = 16 ;

localparam [AWIDTH:0] MAP      ={
  AWIDTH                                     
                                              };

module GOOD();

endmodule

module top();

  parameter D =MAP;

  if (D == 17'b00000000000000000000000000010000) begin
     GOOD good();
  end
   
endmodule
