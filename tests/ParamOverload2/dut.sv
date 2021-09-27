package keymgr_pkg;
   typedef logic [63:0][5:0] lfsr_perm_t;
   parameter lfsr_perm_t RndCnstLfsrPermDefault = {
      128'h16108c9f9008aa37e5118d1ec1df64a7,
      256'h24f3f1b73537f42d38383ee8f897286df81d49ab54b6bbbb666cbd1a16c41252
   };
endpackage // keymgr_pkg

module keymgr;
   import keymgr_pkg::*;
   parameter lfsr_perm_t RndCnstLfsrPerm = RndCnstLfsrPermDefault;
endmodule // keymgr

module top;
   keymgr #(
      .RndCnstLfsrPerm(384'b1)
   ) u_keymgr ();
endmodule // top
