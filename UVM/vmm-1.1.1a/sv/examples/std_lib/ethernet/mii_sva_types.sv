// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    All Rights Reserved Worldwide
// 
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
// 
//        http://www.apache.org/licenses/LICENSE-2.0
// 
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
// 


`ifndef MII_SVA_TYPES__SV
`define MII_SVA_TYPES__SV

  localparam int mii_sva_error_flag_size    = 20;
  localparam int mii_sva_cover_flag_size    = 13;

  typedef bit [1:mii_sva_error_flag_size] mii_sva_error_size_type;
  typedef bit [1:mii_sva_cover_flag_size] mii_sva_cover_size_type;

  // error flags
  typedef enum mii_sva_error_size_type {
    MII_TX_x_z                = mii_sva_error_size_type'('b1),                  // 1
    MII_TX_NO_CRS_W_COL       = mii_sva_error_size_type'('b10),                 // 2
    MII_TX_EN_ASSERT_WHEN_CRS = mii_sva_error_size_type'('b100),                // 3
    MII_TX_EN_ER_01           = mii_sva_error_size_type'('b1000),               // 4
    MII_TX_BAD_PREAMBLE       = mii_sva_error_size_type'('b10000),              // 5
    MII_TX_BAD_LOW_SDF        = mii_sva_error_size_type'('b100000),             // 6
    MII_TX_BAD_HIGH_SDF       = mii_sva_error_size_type'('b1000000),            // 7
    MII_TX_ODD_NIBBLES        = mii_sva_error_size_type'('b10000000),           // 8
    MII_TX_CRS_NOT_ASSERTED   = mii_sva_error_size_type'('b100000000),          // 9
    MII_TX_NOT_A_JAM          = mii_sva_error_size_type'('b1000000000),         // 10
    MII_TX_FCS_VALID_W_JAM    = mii_sva_error_size_type'('b10000000000),        // 11
    MII_TX_BAD_FCS            = mii_sva_error_size_type'('b100000000000),       // 12
    MII_TX_LATE_COL           = mii_sva_error_size_type'('b1000000000000),      // 13
    MII_TX_SHORT_FRAME        = mii_sva_error_size_type'('b10000000000000),     // 14
    MII_TX_TAGGED_FRAME_LONG  = mii_sva_error_size_type'('b100000000000000),    // 15
    MII_TX_NORMAL_FRAME_LONG  = mii_sva_error_size_type'('b1000000000000000),   // 16
    MII_TX_TAGGED_BAD_LENGTH  = mii_sva_error_size_type'('b10000000000000000),  // 17
    MII_TX_NORMAL_BAD_LENGTH  = mii_sva_error_size_type'('b100000000000000000), // 18
    MAC_TX_SHORT_INTERFR_GAP  = mii_sva_error_size_type'('b1000000000000000000),// 19
    MAC_TX_BIG_RETRANS_GAP    = mii_sva_error_size_type'('b10000000000000000000)// 20
                                                            } mii_sva_tx_error_type;

  typedef enum mii_sva_cover_size_type {
    MII_TX_COL_ON_SYMBOL_0    = mii_sva_cover_size_type'('b1),               // 1
    MII_TX_COL_ALMOST_LATE    = mii_sva_cover_size_type'('b10),              // 2
    MII_TX_COL_EARLIEST_LATE  = mii_sva_cover_size_type'('b100),             // 3
    MII_TX_COL_LATE           = mii_sva_cover_size_type'('b1000),            // 4
    MII_TX_COL_LAST           = mii_sva_cover_size_type'('b10000),           // 5
    MII_TX_UNTAGGED_FRAME     = mii_sva_cover_size_type'('b100000),          // 6
    MII_TX_TAGGED_FRAME       = mii_sva_cover_size_type'('b1000000),         // 7
    MII_TX_ER_DETECTED        = mii_sva_cover_size_type'('b10000000),        // 8
    MII_TX_RESET_DETECTED     = mii_sva_cover_size_type'('b100000000),       // 9
    MII_TX_MIN_INTERFRAME     = mii_sva_cover_size_type'('b1000000000),      // 10
    MII_TX_NORMAL_INTERFRAME  = mii_sva_cover_size_type'('b10000000000),     // 11
    MII_TX_RETRANS_INTERFRAME = mii_sva_cover_size_type'('b1000000000000)    // 12
                                                                         // 13
                                                             } mii_sva_tx_cover_type;

  typedef enum mii_sva_error_size_type {
    MII_RX_x_z                = mii_sva_error_size_type'('b1),                  // 1
    MII_RX_CRS_NOT_W_COL      = mii_sva_error_size_type'('b10),                 // 2
                                                                            // 3
                                                                            // 4
                                                                            // 5
                                                                            // 6
    MII_RX_BAD_OR_NO_SDF      = mii_sva_error_size_type'('b1000000),            // 7
    MII_RX_ODD_NIBBLES        = mii_sva_error_size_type'('b10000000),           // 8
    MII_RX_CRS_NOT_ASSERTED   = mii_sva_error_size_type'('b100000000),          // 9
                                                                            // 10
                                                                            // 11
    MII_RX_BAD_FCS            = mii_sva_error_size_type'('b100000000000),       // 12
    MII_RX_LATE_COL           = mii_sva_error_size_type'('b1000000000000),      // 13
    MII_RX_SHORT_FRAME        = mii_sva_error_size_type'('b10000000000000),     // 14
    MII_RX_TAGGED_FRAME_LONG  = mii_sva_error_size_type'('b100000000000000),    // 15
    MII_RX_NORMAL_FRAME_LONG  = mii_sva_error_size_type'('b1000000000000000),   // 16
    MII_RX_TAGGED_BAD_LENGTH  = mii_sva_error_size_type'('b10000000000000000),  // 17
    MII_RX_NORMAL_BAD_LENGTH  = mii_sva_error_size_type'('b100000000000000000), // 18
    MII_RX_SHORT_INTERFR_GAP  = mii_sva_error_size_type'('b1000000000000000000),// 19
    MII_RX_DV_ER_D_01_NOT1110 = mii_sva_error_size_type'('b10000000000000000000)// 20
                                                             } mii_sva_rx_error_type;

  typedef enum mii_sva_cover_size_type  {
    MII_RX_COL_ON_SYMBOL_0    = mii_sva_cover_size_type'('b1),             // 1
    MII_RX_COL_ALMOST_LATE    = mii_sva_cover_size_type'('b10),            // 2
    MII_RX_COL_EARLIEST_LATE  = mii_sva_cover_size_type'('b100),           // 3
    MII_RX_COL_LATE           = mii_sva_cover_size_type'('b1000),          // 4
    MII_RX_COL_LAST           = mii_sva_cover_size_type'('b10000),         // 5
    MII_RX_UNTAGGED_FRAME     = mii_sva_cover_size_type'('b100000),        // 6
    MII_RX_TAGGED_FRAME       = mii_sva_cover_size_type'('b1000000),       // 7
    MII_RX_ER_DETECTED        = mii_sva_cover_size_type'('b10000000),      // 8
    MII_RX_RESET_DETECTED     = mii_sva_cover_size_type'('b100000000),     // 9
                                                                       // 10
                                                                       // 11
                                                                       // 12
    MII_RX_FALSE_CARRIER      = mii_sva_cover_size_type'('b1000000000000)  // 13
                                                            } mii_sva_rx_cover_type;

  // Interrogation functions for status flags
  function bit mii_sva_get_error_bit(
            input mii_sva_error_size_type FrameError, 
            input mii_sva_error_size_type positions);
    return (|(FrameError & positions));
  endfunction

  function bit mii_sva_get_cover_bit(
            input mii_sva_cover_size_type FrameCover, 
            input mii_sva_cover_size_type positions);
    return (|(FrameCover & positions));
  endfunction

`endif
