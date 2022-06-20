package uvm;
typedef struct packed {
  int unsigned exp_bits;
  int unsigned man_bits;
} fp_encoding_t;
parameter NUM_FP_FORMATS = 4;

localparam fp_encoding_t [0:NUM_FP_FORMATS-1] FP_ENCODINGS  = '{
  '{8,  23}, // IEEE binary32 (single)
  '{11, 52}, // IEEE binary64 (double)
  '{5,  10}, // IEEE binary16 (half)
  '{5,  2},  // custom binary8
  '{8,  7}   // custom binary16alt
  // add new formats here
};

function automatic int unsigned fp_width(fp_format_e fmt);
return FP_ENCODINGS[fmt].exp_bits + FP_ENCODINGS[fmt].man_bits + 1;
endfunction

endpackage
