package my_pkg;
   function automatic logic [7:0] sbox4_8bit(logic [7:0] state_in);
      return state_in;
   endfunction : sbox4_8bit

   function automatic logic [15:0] sbox4_16bit(logic [15:0] state_in);
      logic [15:0] state_out;
      state_out[0 +: 8] = sbox4_8bit(state_in[0 +: 8]);
      return state_out;
   endfunction : sbox4_16bit
endpackage // my_pkg

module top(output logic [15:0] o);
   assign o = my_pkg::sbox4_16bit(16'hABCD);
endmodule // top

