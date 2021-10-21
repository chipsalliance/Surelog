package fpnew_pkg;
   
typedef struct packed {
    int unsigned Width;
    logic        EnableNanBox;
  } fpu_features_t;

endpackage // fpnew_pkg

 module fpnew_top #(
  // FPU configuration
  parameter fpnew_pkg::fpu_features_t       Features       = fpnew_pkg::RV64D_Xsflt
		   ) ();
 endmodule

module fpu_wrap ();

localparam fpnew_pkg::fpu_features_t FPU_FEATURES = '{
      Width:         64,
      EnableNanBox:  1'b1
    };
     
       fpnew_top #(
      .Features       ( FPU_FEATURES              )
		   ) i_fpnew_bulk ();
        
endmodule
