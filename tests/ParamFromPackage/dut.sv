package aes_pkg;
   parameter logic [7:0][3:0] X = 32'habcd;
endpackage // aes_pkg

module aes_cipher_core import aes_pkg::*;
   #(
      parameter logic [7:0][3:0] P = X,
      parameter logic Z = 0
   );
endmodule // aes_cipher_core

module top;
   aes_cipher_core #(.Z(1)) u_aes_cipher_core();
endmodule
