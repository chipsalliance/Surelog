module kmac_core#(
  // EnMasking: Enable masking security hardening inside keccak_round
  // If it is enabled, the result digest will be two set of 1600bit.
  parameter  bit EnMasking = 0,
  localparam int Share = (EnMasking) ? 2 : 1 // derived parameter
) (
  
  input                             kmac_en_i,
  input sha3_pkg::keccak_strength_e strength_i

);

  //import sha3_pkg::*;
   
  import sha3_pkg::KeccakCountW;
  import sha3_pkg::KeccakRate;
  import sha3_pkg::L128;
  import sha3_pkg::L224;
  import sha3_pkg::L256;
  import sha3_pkg::L384;
  import sha3_pkg::L512;
   
 logic [sha3_pkg::KeccakCountW-1:0] block_addr_limit;
    always_comb begin
    unique case (strength_i)
      L128: block_addr_limit = KeccakCountW'(KeccakRate[L128]);
      L224: block_addr_limit = KeccakCountW'(KeccakRate[L224]);
      L256: block_addr_limit = KeccakCountW'(KeccakRate[L256]);
      L384: block_addr_limit = KeccakCountW'(KeccakRate[L384]);
      L512: block_addr_limit = KeccakCountW'(KeccakRate[L512]);

      default: block_addr_limit = '0;
    endcase
    end // always_comb

endmodule
