package pinmux_pkg;
   typedef enum int {
      A = 1
   } enum1_e;

   typedef struct packed {
      enum1_e dio_pad_type;
   } struct1_t;

   typedef enum int {
      B = 2
   } enum2_e;

   typedef struct packed {
      enum2_e dio_pad_type;
   } struct2_t;
endpackage : pinmux_pkg

module prim_generic_pad_attr(output int o);
   parameter int PadTypeInGeneric = 0;
   assign o = PadTypeInGeneric;
endmodule : prim_generic_pad_attr

module prim_submodule(output int o);
   parameter int PadType = 0;

   prim_generic_pad_attr #(
       .PadTypeInGeneric(PadType)
   ) u_impl_generic(
      .o(o)
   );
endmodule


module prim_pad_attr();
   parameter int PadType = 0;

   prim_submodule #(
      .PadType(PadType)
   ) u_submodule(
      .o(o)
   );
   
endmodule

module almost_top();
   import pinmux_pkg::*;
   parameter struct1_t TargetCfg = 1;

   prim_pad_attr #(
      .PadType(TargetCfg.dio_pad_type)
   ) u_prim_pad_attr(
   
   );
endmodule

module top();
   import pinmux_pkg::*;
   parameter struct2_t TargetCfg = 2;

   almost_top

     u_top(
   
   );
endmodule
