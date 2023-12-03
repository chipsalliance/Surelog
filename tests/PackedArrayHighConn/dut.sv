package prim_pad_wrapper_pkg;
  typedef enum logic [2:0] {
    BidirStd = 3'h0
  } pad_type_e;
  typedef logic [7:0] pad_pok_t;
endpackage : prim_pad_wrapper_pkg

module prim_pad_wrapper
  import prim_pad_wrapper_pkg::*; (input pad_pok_t pok_i);
endmodule : prim_pad_wrapper

module dut
  import prim_pad_wrapper_pkg::*; #(parameter logic [0:0][1:0] DioPadBank = '0) ();
  pad_pok_t [3:0] pad_pok;
  prim_pad_wrapper u_dio_pad (
    .pok_i      ( pad_pok[DioPadBank[0]]   )
  );
endmodule : dut


/*
module dut (
  //  input logic [3:0] a,
  //  input logic [3:0] b,
  //  output logic [1:0][3:0] out
);

   // typedef logic [3:0] logic4;

    logic [1:0] vector2x4;

   // logic4 [1:0] vector2x4;
   // assign vector2x4[0] = a;
   // assign vector2x4[1] = b;

  //  assign out = vector2x4;

endmodule
*/

/*
module top(output logic [9:0] o);
   typedef struct packed {
      logic [9:0] min_v;
   } filter_ctl_t;

   filter_ctl_t [1:0] a = '{10'd15, 10'd0};
   assign o = a[1];
endmodule
*/


/*

package pack_pkg;
typedef enum logic { fOO } foo;
endpackage

module dut(input pack_pkg::foo [1:0] inp[2], output pack_pkg::foo [1:0] out[2]);
assign out = inp;
endmodule

*/