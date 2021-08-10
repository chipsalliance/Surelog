package aes_pkg;
   parameter logic [159:0] RndCnstMaskingLfsrSeedDefault =
      160'hc132b5723c5a4cf4743b3c7c32d580f74f1713a;
endpackage // aes_pkg

module aes_cipher_core import aes_pkg::*;();
   parameter logic [159:0] RndCnstMaskingLfsrSeed = 0;
endmodule // aes_cipher_core

module aes_core import aes_pkg::*;();
   aes_cipher_core #(
      .RndCnstMaskingLfsrSeed(RndCnstMaskingLfsrSeedDefault)
   ) u_aes_cipher_core ();
endmodule // aes_core


