package  fpnew_pkg;
   
  localparam int unsigned NUM_FP_FORMATS = 5;
  localparam int unsigned FP_FORMAT_BITS = $clog2(NUM_FP_FORMATS);

 typedef struct packed {
    int unsigned exp_bits;
    int unsigned man_bits;
  } fp_encoding_t;
   
  typedef enum logic [FP_FORMAT_BITS-1:0] {
    FP32    = 'd0,
    FP64    = 'd1,
    FP16    = 'd2,
    FP8     = 'd3,
    FP16ALT = 'd4
    // add new formats here
  } fp_format_e;

  localparam fp_encoding_t [0:NUM_FP_FORMATS-1] FP_ENCODINGS  = '{
    '{8,  23}, // IEEE binary32 (single)
    '{11, 52}, // IEEE binary64 (double)
    '{5,  10}, // IEEE binary16 (half)
    '{5,  2},  // custom binary8
    '{8,  7}   // custom binary16alt
    // add new formats here
  };

  localparam fpu_features_t RV64D_Xsflt = '{
    Width:         64,
    EnableVectors: 1'b1,
    EnableNanBox:  1'b1,
    FpFmtMask:     5'b11111,
    IntFmtMask:    4'b1111
  };
   
  function automatic int unsigned fp_width(fp_format_e fmt);
    return FP_ENCODINGS[fmt].exp_bits + FP_ENCODINGS[fmt].man_bits + 1;
  endfunction
   
endpackage 

module top();
   localparam int unsigned NUM_FORMATS  = fpnew_pkg::NUM_FP_FORMATS;
   parameter fpnew_pkg::fpu_features_t       Features       = fpnew_pkg::RV64D_Xsflt;
   parameter WIDTH = Features.Width;
   

  for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : gen_nanbox_check
    localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));

    if (Features.EnableNanBox && (FP_WIDTH < WIDTH)) begin : check
      for (genvar op = 0; op < int'(NUM_OPERANDS); op++) begin : operands
        assign is_boxed[fmt][op] = (!vectorial_op_i)
                                   ? operands_i[op][WIDTH-1:FP_WIDTH] == '1
                                   : 1'b1;
      end
    end else begin : no_check
      assign is_boxed[fmt] = '1;
    end
     
  end
   
endmodule
     
