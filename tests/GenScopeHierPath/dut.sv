package prim_pad_wrapper_pkg;
   typedef enum  logic [2:0] {
      A = 3'h0,
      B = 3'h1
   } pad_type_e;
endpackage : prim_pad_wrapper_pkg

package pinmux_pkg;
   import prim_pad_wrapper_pkg::*;

   parameter int NDioPads = 4;

   typedef struct packed {
      pad_type_e [NDioPads-1:0] dio_pad_type;
   } target_cfg_t;

   parameter target_cfg_t DefaultTargetCfg = '{
      dio_pad_type: {NDioPads{B}}
   };
endpackage : pinmux_pkg


module prim_generic_pad_attr(output int a);
   import prim_pad_wrapper_pkg::*;
   parameter pad_type_e PadType = A;
   if (PadType == B) begin : gen_assign
      assign a = 1;
   end
endmodule : prim_generic_pad_attr


module prim_pad_attr(output int b);
   import prim_pad_wrapper_pkg::*;
   parameter pad_type_e PadType = A;

   if (1) begin : gen_generic
      prim_generic_pad_attr #(
         .PadType(PadType)
      ) u_impl_generic(.a(b));
   end

endmodule

module top(output int o);
   import pinmux_pkg::*;
   parameter target_cfg_t TargetCfg = DefaultTargetCfg;

  for (genvar k = 0; k < NDioPads; k++) begin : gen_dio_attr
     prim_pad_attr #(
        .PadType(TargetCfg.dio_pad_type[k])
     ) u_prim_pad_attr(.b(o));
  end
endmodule
