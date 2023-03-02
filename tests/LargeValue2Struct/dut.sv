package pack;
  parameter int SramKeyWidth      = 128;
  
  typedef logic [SramKeyWidth-1:0]   sram_key_t;
  typedef logic [SramKeyWidth-1:0] sram_nonce_t;

typedef struct packed {
    sram_key_t   key;
    sram_nonce_t nonce;
  } scrmbl_key_init_t;

localparam scrmbl_key_init_t RndCnstScrmblKeyInitDefault =
      256'hcebeb96ffe0eced795f8b2cfe23c1e519e4fa08047a6bcfb811b04f0a479006e;
endpackage

module prim_sec_anchor_flop #(
  parameter int               Width      = 1, 
  parameter logic [Width-1:0] ResetValue = 0) ();
endmodule

module top();
import pack::*;
parameter scrmbl_key_init_t RndCnstScrmblKeyInit = RndCnstScrmblKeyInitDefault;
parameter Width = SramKeyWidth;
prim_sec_anchor_flop #(
    .Width(Width),
    .ResetValue(RndCnstScrmblKeyInit.key)
  ) u_key_out_anchor (
  );
endmodule