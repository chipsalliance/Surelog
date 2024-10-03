module kmac#(
  // EnMasking: Enable masking security hardening inside keccak_round
  // If it is enabled, the result digest will be two set of 1600bit.
  parameter  bit EnMasking = 0,
  localparam int Share = (EnMasking) ? 2 : 1 // derived parameter
) (
 
  input                             kmac_en_i,
  input sha3_pkg::keccak_strength_e strength_i

);

   kmac_core core (.*);
   

endmodule
