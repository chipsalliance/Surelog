
package prim_mubi_pkg;
parameter int MuBi4Width = 4;
typedef enum logic [MuBi4Width-1:0] {
  MuBi4True = 4'hA, // enabled
  MuBi4False = 4'h5  // disabled
} mubi4_t;

endpackage

package pkg;

typedef enum logic [9:0] {
  ReadingLow  = {6'b001100, prim_mubi_pkg::MuBi4False}
} fsm_state_e;

endpackage // pkg

module GOOD();
endmodule
   
module top();

   if (pkg::ReadingLow == 197) begin
      GOOD good();
   end

endmodule
