module otp_ctrl_ecc_reg(output int a);
   parameter  int Depth = 999;
   localparam int Aw = $clog2(Depth);
   assign a = Aw;
endmodule : otp_ctrl_ecc_reg

module top(output int o);
   typedef struct packed {
      int x;
   } part_info_t;

   parameter part_info_t Info = part_info_t'(10);
   localparam int NumScrmblBlocks = Info.x;

   otp_ctrl_ecc_reg #(
      .Depth (NumScrmblBlocks)
   ) u_otp_ctrl_ecc_reg (
      .a(o));
endmodule : top
