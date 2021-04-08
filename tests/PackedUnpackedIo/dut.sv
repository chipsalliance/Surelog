package hmac_pkg;
typedef logic [31:0] sha_word_t;
function automatic sha_word_t [7:0] 
                           compress( 
                                              input sha_word_t w, 
                                              input sha_word_t ww [16:0], 
                                              input sha_word_t [7:0] h_i,
                                              input sha_word_t [7:0] hh_ii [16:0],
                                              input logic hh [16:0],
                                              input logic [7:0] ii [16:0]);
 
endfunction
endpackage
