
package lc_ctrl_pkg;

  parameter logic [15:0] A10 = 16'h0000;
  parameter logic [15:0] A11 = 16'h0000;

 

  // TODO: make this secret and generate randomly, given a specific ECC polynomial.
  typedef enum logic [LcStateWidth-1:0] {
    // Halfword idx   :  11 | 10 |  9 |  8 |  7 |  6 |  5 |  4 |  3 |  2 |  1 |  0
    LcStRaw           = '0,
    LcStTestUnlocked0 = {A11, A10}
  } lc_state_e;
endpackage

//------------------------------------------------------------------------------------------------
 
package otp_ctrl_reg_pkg;

  // Param list
  parameter int NumSramKeyReqSlots = 2;
  parameter int OtpByteAddrWidth = 11;
  parameter int NumErrorEntries = 9;

endpackage

package otp_ctrl_pkg;

  import prim_util_pkg::vbits;
  import otp_ctrl_reg_pkg::*;

  // OTP-macro specific
  parameter int OtpWidth         = 16;
  parameter int OtpAddrWidth     = OtpByteAddrWidth - $clog2(OtpWidth/8);

endpackage
