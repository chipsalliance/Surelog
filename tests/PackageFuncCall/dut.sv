package prim_cipher_pkg;
 
  parameter logic [15:0][3:0] PRESENT_SBOX4 = {4'h2, 4'h1, 4'h7, 4'h4,
                                               4'h8, 4'hF, 4'hE, 4'h3,
                                               4'hD, 4'hA, 4'h0, 4'h9,
                                               4'hB, 4'h6, 4'h5, 4'hC};
 
  function automatic logic [63:0] sbox4_64bit(logic [63:0] state_in, logic [15:0][3:0] sbox4);
    logic [63:0] state_out;
    // note that if simulation performance becomes an issue, this loop can be unrolled
    for (int k = 0; k < 64/4; k++) begin
      state_out[k*4  +: 4] = sbox4[state_in[k*4  +: 4]];
    end
    return state_out;
  endfunction : sbox4_64bit

   
  parameter logic [11:0][63:0] PRINCE_ROUND_CONST = {64'hC0AC29B7C97C50DD,
                                                        64'hD3B5A399CA0C2399};


   
endpackage : prim_cipher_pkg


module top();

assign data_state_sbox = prim_cipher_pkg::sbox4_64bit(data_state_xor,
                       prim_cipher_pkg::PRESENT_SBOX4);

 always_comb begin : p_post_round_xor
           data_o  = data_state[2*NumRoundsHalf+1] ^
                     prim_cipher_pkg::PRINCE_ROUND_CONST
                     [11]
                     [DataWidth-1:0];
          data_o ^= k1;
           data_o ^= k0_prime;
         end


   
endmodule
