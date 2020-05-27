package prim_pkg;

  // Implementation target specialization
  typedef enum integer {
    ImplGeneric = 1,
    ImplXilinx  = 0
  } impl_e;

endpackage

module prim_diff_decode ();
  parameter prim_pkg::impl_e Impl = prim_pkg::ImplGeneric;


    import prim_pkg::*;

    if (Impl == ImplGeneric) begin : gen_pad_generic

    always_comb begin : p_diff_fsm
     
      unique case (state_q)
        // we remain here as long as
        // the diff pair is correctly encoded
        IsSkewed: begin
            state_d = IsStd;
        end
        default : ;
      endcase
    end

  end

endmodule // prim_diff_decode
