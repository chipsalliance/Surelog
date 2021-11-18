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

   typedef enum int {
      C = 3
   } enum3_e;

   typedef struct packed {
      enum3_e dio_pad_type;
   } struct3_t;
endpackage 

module prim_generic();
   parameter int PadTypeInGeneric = 0;
   assign o = PadTypeInGeneric;                  // assigning value of TargetCfg.dio_pad_type
endmodule 

module prim_submodule();
   parameter int PadType = 0;

   prim_generic #(
       .PadTypeInGeneric(PadType)
   ) u_impl_generic(
      
   );
endmodule

module prim_pad_attr();
   import pinmux_pkg::*;
   parameter struct3_t TargetCfg = 77;           // unused parameter
   parameter int PadType = 0;
  
   prim_submodule #(
      .PadType(PadType)
   ) u_submodule(
     
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
   parameter struct2_t TargetCfg = 20;               // assigning value of TargetCfg

   almost_top #(
      .TargetCfg(TargetCfg)
   ) u_top(
      
   );
endmodule

