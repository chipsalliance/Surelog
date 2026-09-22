// A packed assignment pattern whose elements are WIDER than one bit and whose
// total width exceeds 64 bits.
//
// adjustOpSize() derived the per-element width as fullSize / innerSize, but
// innerSize is the INNERMOST dimension -- i.e. the element width -- so that
// expression yields the element COUNT.  The two coincide only on a SQUARE
// array, which is why `sq` below always folded correctly while `ns` and `wide`
// did not: every element was given 16 bits instead of 8, so the bit vector
// overflowed and only the first half of the elements survived, each preceded
// by 8 zero bits.  The subsequent pack into a uint64_t then shifted by up to
// 255, which is undefined behaviour, so the constant came out as garbage.
module top;
  // square, 64 bits -- folded correctly before the fix too
  parameter logic [7:0][7:0]  sq   = '{8'h88, 8'h77, 8'h66, 8'h55,
                                       8'h44, 8'h33, 8'h22, 8'h11};
  // NOT square, still <= 64 bits
  parameter logic [7:0][3:0]  narrow = '{4'h8, 4'h7, 4'h6, 4'h5,
                                         4'h4, 4'h3, 4'h2, 4'h1};
  // not square, > 64 bits: needs a BIN constant, a uint64_t cannot hold it
  parameter logic [15:0][7:0] wide = '{8'hf0, 8'he0, 8'hd0, 8'hc0,
                                       8'hb0, 8'ha0, 8'h90, 8'h80,
                                       8'h70, 8'h60, 8'h50, 8'h40,
                                       8'h30, 8'h20, 8'h10, 8'h01};
  // 1-D: here the elements really ARE bits, and fullSize / innerSize == 1 is
  // the right answer -- the fallback must keep working
  parameter logic [3:0]       bits = '{1'b1, 1'b0, 1'b1, 1'b1};
endmodule
