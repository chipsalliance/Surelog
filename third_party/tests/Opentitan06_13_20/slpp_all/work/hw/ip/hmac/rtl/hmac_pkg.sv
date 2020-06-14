// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package hmac_pkg;

  // this currently uses the
  // fully asynchronous implemenation
  localparam int NumAlerts = 1;
  localparam logic [NumAlerts-1:0] AlertAsyncOn = NumAlerts'(1'b1);

  localparam int MsgFifoDepth = 16;

  localparam int NumRound = 64;   // SHA-224, SHA-256

  typedef logic [31:0] sha_word_t;
  localparam int WordByte = $bits(sha_word_t)/8;

  typedef struct packed {
    sha_word_t           data;
    logic [WordByte-1:0] mask;
  } sha_fifo_t;


  localparam sha_word_t InitHash [8]= '{
    32'h6a09_e667, 32'hbb67_ae85, 32'h3c6e_f372, 32'ha54f_f53a,
    32'h510e_527f, 32'h9b05_688c, 32'h1f83_d9ab, 32'h5be0_cd19
  };

  localparam sha_word_t CubicRootPrime [64] = '{
    32'h428a_2f98, 32'h7137_4491, 32'hb5c0_fbcf, 32'he9b5_dba5,
    32'h3956_c25b, 32'h59f1_11f1, 32'h923f_82a4, 32'hab1c_5ed5,
    32'hd807_aa98, 32'h1283_5b01, 32'h2431_85be, 32'h550c_7dc3,
    32'h72be_5d74, 32'h80de_b1fe, 32'h9bdc_06a7, 32'hc19b_f174,
    32'he49b_69c1, 32'hefbe_4786, 32'h0fc1_9dc6, 32'h240c_a1cc,
    32'h2de9_2c6f, 32'h4a74_84aa, 32'h5cb0_a9dc, 32'h76f9_88da,
    32'h983e_5152, 32'ha831_c66d, 32'hb003_27c8, 32'hbf59_7fc7,
    32'hc6e0_0bf3, 32'hd5a7_9147, 32'h06ca_6351, 32'h1429_2967,
    32'h27b7_0a85, 32'h2e1b_2138, 32'h4d2c_6dfc, 32'h5338_0d13,
    32'h650a_7354, 32'h766a_0abb, 32'h81c2_c92e, 32'h9272_2c85,
    32'ha2bf_e8a1, 32'ha81a_664b, 32'hc24b_8b70, 32'hc76c_51a3,
    32'hd192_e819, 32'hd699_0624, 32'hf40e_3585, 32'h106a_a070,
    32'h19a4_c116, 32'h1e37_6c08, 32'h2748_774c, 32'h34b0_bcb5,
    32'h391c_0cb3, 32'h4ed8_aa4a, 32'h5b9c_ca4f, 32'h682e_6ff3,
    32'h748f_82ee, 32'h78a5_636f, 32'h84c8_7814, 32'h8cc7_0208,
    32'h90be_fffa, 32'ha450_6ceb, 32'hbef9_a3f7, 32'hc671_78f2
  };

  function automatic sha_word_t conv_endian( input sha_word_t v, input logic swap);
    sha_word_t conv_data = {<<8{v}};
    conv_endian = (swap) ? conv_data : v ;
  endfunction : conv_endian

  function automatic sha_word_t rotr( input sha_word_t v , input int amt );
    rotr = (v >> amt) | (v << (32-amt));
  endfunction : rotr

  function automatic sha_word_t shiftr( input sha_word_t v, input int amt );
    shiftr = (v >> amt);
  endfunction : shiftr

  function automatic sha_word_t [7:0] compress( input sha_word_t w, input sha_word_t k,
                                                input sha_word_t [7:0] h_i);
    automatic sha_word_t sigma_0, sigma_1, ch, maj, temp1, temp2;

    sigma_1 = rotr(h_i[4], 6) ^ rotr(h_i[4], 11) ^ rotr(h_i[4], 25);
    ch = (h_i[4] & h_i[5]) ^ (~h_i[4] & h_i[6]);
    temp1 = (h_i[7] + sigma_1 + ch + k + w);
    sigma_0 = rotr(h_i[0], 2) ^ rotr(h_i[0], 13) ^ rotr(h_i[0], 22);
    maj = (h_i[0] & h_i[1]) ^ (h_i[0] & h_i[2]) ^ (h_i[1] & h_i[2]);
    temp2 = (sigma_0 + maj);

    compress[7] = h_i[6];          // h = g
    compress[6] = h_i[5];          // g = f
    compress[5] = h_i[4];          // f = e
    compress[4] = h_i[3] + temp1;  // e = (d + temp1)
    compress[3] = h_i[2];          // d = c
    compress[2] = h_i[1];          // c = b
    compress[1] = h_i[0];          // b = a
    compress[0] = (temp1 + temp2); // a = (temp1 + temp2)
  endfunction : compress

  function automatic sha_word_t calc_w(input sha_word_t w_0,
                                       input sha_word_t w_1,
                                       input sha_word_t w_9,
                                       input sha_word_t w_14);
    automatic sha_word_t sum0, sum1;
    sum0 = rotr(w_1,   7) ^ rotr(w_1,  18) ^ shiftr(w_1,   3);
    sum1 = rotr(w_14, 17) ^ rotr(w_14, 19) ^ shiftr(w_14, 10);
    calc_w = w_0 + sum0 + w_9 + sum1;
  endfunction : calc_w

  typedef enum logic [31:0] {
    NoError                    = 32'h0000_0000,
    SwPushMsgWhenShaDisabled   = 32'h0000_0001,
    SwHashStartWhenShaDisabled = 32'h0000_0002,
    SwUpdateSecretKeyInProcess = 32'h0000_0003,
    SwHashStartWhenActive      = 32'h0000_0004,
    SwPushMsgWhenDisallowed    = 32'h0000_0005
  } err_code_e;

endpackage : hmac_pkg
