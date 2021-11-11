module prim_subreg;
   parameter logic [4:0] RESVAL = '0;
   int a = int'(RESVAL);
endmodule // prim_subreg

module prim_subreg_shadow;
   typedef struct packed {
      logic [2:0] a;
      logic [1:0] b;
   } struct_t;

   typedef enum logic [2:0] {
      ENUM_ITEM = 3'b000
   } enum_t;

   parameter struct_t RESVAL = '{
      a: ENUM_ITEM,
      b: '1
   };

   prim_subreg #(
      .RESVAL(RESVAL)
   ) staged_reg ();
endmodule // prim_subreg_shadow

module top;
   typedef struct packed {
      logic [1:0] a;
      logic [2:0] b;
   } struct_t;

   typedef enum logic [1:0] {
      ENUM_ITEM = 2'b11
   } enum_t;

   parameter struct_t CTRL_RESET = '{
      a: ENUM_ITEM,
      b: '0
   };

   prim_subreg_shadow #(
      .RESVAL(CTRL_RESET)
   ) u_ctrl_reg_shadowed ();
endmodule // top
