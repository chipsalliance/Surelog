package otp_ctrl_part_pkg;
   parameter logic [2:0] PartInvDefault = 3'({
                                              3'({
                                                  3'h1
                                                  })
                                              });
endpackage : otp_ctrl_part_pkg

module top(output int o);
   import otp_ctrl_part_pkg::*;

   parameter P = PartInvDefault;

   logic [$bits(PartInvDefault)/1-1:0] part_buf_data = '1;
   assign o = int'(part_buf_data);
endmodule
