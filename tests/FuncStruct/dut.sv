package hmac_pkg;
typedef logic [31:0] sha_word_t;
function automatic sha_word_t [7:0] compress( input sha_word_t w, input sha_word_t [7:0] h_i = 0);
  automatic sha_word_t sigma_0;

  sigma_0 = 32'h11111111;
  compress[0] = (sigma_0);
endfunction// : compress
endpackage


module dut import hmac_pkg::*; (
);
sha_word_t [15:0] w;
sha_word_t [7:0] hash;
assign w[0] = 32'h00000000;
assign hash = compress(w[0], hash);

endmodule
