module top(input logic clk, output logic[3:0] o);
   typedef enum logic [3:0] {
        REF      = 4'b0001,
        DESELECT = 4'b1xxx
   } dfi_cmd_e;

   assign o = DESELECT;
endmodule
