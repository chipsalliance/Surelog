
module prim_subreg;
   parameter logic [4:0] RESVAL = '0;
   int a = int'(RESVAL);
endmodule // prim_subreg

module prim_subreg_shadow;
   typedef struct packed {
      logic [2:0] a;
      logic [1:0] b;
   } struct_ab;

   parameter struct_ab RESVAL = '{
      a: '0,
      b: '1
   };

   prim_subreg #(
      .RESVAL(RESVAL)
   ) staged_reg();
   
endmodule // prim_subreg_shadow

module top;
   typedef struct packed {
      logic [1:0] a;
      logic [2:0] b;
   } struct_ab;
   parameter v1 = 1;
   parameter v2 = 0;
   
   parameter struct_ab CTRL_RESET = '{
    //  a: '1,
    //  b: '0
    v1, v2
   };

   prim_subreg_shadow #(
      .RESVAL(CTRL_RESET)
   ) u_ctrl_reg_shadowed();
endmodule // top


