module GOOD ();
endmodule

module top();

typedef logic [0:4]       fmt_logic_t;

typedef struct packed {
    int unsigned Width;
    logic        EnableVectors;
    logic        EnableNanBox;
    fmt_logic_t  FpFmtMask;
    fmt_logic_t IntFmtMask;
  } fpu_features_t;

localparam fpu_features_t RV64D_Xsflt = '{
    Width:         64,
    EnableVectors: 1'b1,
    EnableNanBox:  1'b1,
    FpFmtMask:     5'b11111,
    IntFmtMask:    4'b1111
  };
 localparam XLEN = 64;

localparam IS_XLEN64  = (XLEN == 32) ? 1'b0 : 1'b1;
localparam bit RVF = IS_XLEN64;
localparam bit RVD = IS_XLEN64;
localparam bit XF16    = 1'b0;
localparam bit XF16ALT = 1'b0;
localparam bit XF8     = 1'b0;
localparam bit XFVEC   = 1'b0;

localparam fpu_features_t FPU_FEATURES = '{
      Width:         64,
      EnableVectors: XFVEC,
      EnableNanBox:  1'b1,
      FpFmtMask:     {RVF, RVD, XF16, XF8, XF16ALT},
      IntFmtMask:    {XFVEC && XF8, XFVEC && (XF16 || XF16ALT), 1'b1, 1'b1}
    };
 parameter fpu_features_t   Features       = FPU_FEATURES;
 parameter fmt_logic_t      FpFmtMask     = Features.FpFmtMask;

localparam DEBUGME = FpFmtMask[0];

if (FpFmtMask == 5'b11000) begin 
  GOOD good1();
end

if (DEBUGME == 1) begin 
  GOOD good2();
end

endmodule
