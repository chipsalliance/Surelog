package prim_pad_wrapper_pkg;
   parameter int NDioPads = 24;

   typedef enum  logic [2:0] {
      A = 3'h0,
      B = 3'h1
   } pad_type_e;
endpackage : prim_pad_wrapper_pkg

package pinmux_pkg;
   import prim_pad_wrapper_pkg::*;

   typedef struct packed {
      pad_type_e [NDioPads-1:0] dio_pad_type;
   } target_cfg_t;

   parameter target_cfg_t DefaultTargetCfg = '{
      dio_pad_type: {NDioPads{B}}
   };
endpackage : pinmux_pkg


module prim_generic_pad_attr();
   import prim_pad_wrapper_pkg::*;
   parameter pad_type_e PadType = A;
   if (PadType == B) begin : gen_assign
      assign a = 1;
   end
endmodule : prim_generic_pad_attr


module prim_pad_attr();
   import prim_pad_wrapper_pkg::*;
   parameter pad_type_e PadType = A;

   if (1) begin : gen_generic
      prim_generic_pad_attr #(
         .PadType(PadType)
      ) u_impl_generic();
   end
   
endmodule

module top();
   import pinmux_pkg::*;
   parameter target_cfg_t TargetCfg = DefaultTargetCfg;
    prim_pad_attr #(
       .PadType(TargetCfg.dio_pad_type[0])
    ) u_prim_pad_attr();
endmodule
