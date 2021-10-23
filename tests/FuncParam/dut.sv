module prim_lfsr;
   parameter int unsigned LfsrDw = 12;
   function automatic logic [LfsrDw-1:0] compute();
      logic [LfsrDw-1:0] next_state;
      return next_state;
   endfunction 

endmodule

module aes_prng;
   prim_lfsr #(
      .LfsrDw(16)
   ) u_lfsr16();

  prim_lfsr #(
      .LfsrDw(18)
   ) u_lfsr18();

endmodule
