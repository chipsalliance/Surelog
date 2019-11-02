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

//
// SystemVerilog Assertion Checker for MII protocol
// Based on IEE Std 802.3-2002.
//

/*

If an assertion that invalidates a frame fires, it sets TX_FrameError
(resp. RX_FrameError), bits which can be accessed by the testbench.

Cover properties reports through flags TX_FrameCover
(resp. RX_FrameCover).

TX_ER and RX_ER are detected by a cover property as a coverage item.

*/

`ifndef MII_SVA_CHECKER__SV
`define MII_SVA_CHECKER__SV

(* sva_checker *)
interface mii_sva_checker (
        reset_n, TX_CLK, TX_EN, TX_ER, TXD, 
                 COL, CRS, 
                 RX_CLK, RX_DV, RX_ER, RXD,
                 mii_FullDuplex,
                 TX_FrameError, RX_FrameError,
                 TX_FrameCover, RX_FrameCover);


  parameter int severity_level              = 0;
  parameter int minFrameSize                = 64;   // in octets, see 4.4
                // Size in octets = 2 x addressSize + lengthOrTypeSize +
                // tag} + dataSize + crcSize, see 4.2.2.2, (1)
  parameter int maxFrameSize                = 1522; 
  parameter int maxUntaggedFrameSize        = 1518; // in octets, see 4.4
                // min value of Length/Type for Type interpretation
  parameter int minTypeValue                = 1536;
  parameter int mii_TX_max_attempts         = 10;
  parameter bit mii_TX_assume               = 1'b0;
  parameter bit mii_RX_assume               = 1'b0;
  parameter         msg                     = "VIOLATION";
  parameter int category                    = 0;
  parameter int coverage_level_1            = -1;
  parameter int coverage_level_2            = -1;
  parameter int coverage_level_3            = -1;

  input logic reset_n, TX_CLK, TX_EN, TX_ER;
  input logic [3:0] TXD;
  input logic COL, CRS;
  input logic RX_CLK, RX_DV, RX_ER;
  input logic [3:0] RXD;
  input bit         mii_FullDuplex;

// Example 3-11 Disabling a Monitor from an Assertion
  output mii_sva_error_size_type  TX_FrameError;
  output mii_sva_error_size_type  RX_FrameError;
  output mii_sva_cover_size_type  TX_FrameCover;
  output mii_sva_cover_size_type  RX_FrameCover;

  // constants

  localparam
    int MII_D_size = 4, // TXD / RXD size
      addressSize = 6, // 6 octets = 48 bits in compliance with 3.2.3
      lengthOrTypeSize = 2, // 2 octets = 16 bits 
      maxClientDataSize = 1500, // in octets, max MAC client Data,
      crcSize = 4, // 4 octets = 32 bit CRC
      qTagPrefixSize = 4, // in octets, length of QTag Prefix, see 3.5
      maxValidFrame = maxUntaggedFrameSize - 
                      (2 * addressSize + lengthOrTypeSize + crcSize),
                     // in octets, the max length of the MAC client data field
      slotTime = 4096, // MII_D_size, // {# of clk for collision handling, 4.4}
      preambleSize = 7, // 7 octets = 56 bits, see 4.2.5
      sfdSize = 1, // 1 octet = 8 bit start frame delimiter
      headerSize = 8, // 8 octets = 64 bits, sum of preambleSize and sfdSize
      jamSize = 4; // jam sequence 4 octets = 32 bits
  localparam assert_name = "MII_MAC_SVA_CHECKER";

  // types
  typedef logic [3:0] nibble;
  typedef logic [7:0] octet;
  typedef bit [15:0] length_type;

  localparam octet qTagHigh = 8'h81, qTagLow = 8'h00;
  localparam nibble Preamble = 4'h5, SdfH = 4'hD, SdfL = 4'h5;


  // log reporting tasks and common items
`include "sva_std_task.h"

// CRC calculation - may not be used as constraint in Magellan
//   Rajesh Nair, Gerry Ryan, Farivar Farzaneh, "A Symbol Based
//   Algorithm for Hardware Implementation of Cyclic Rdundancy Check
//  (CRC)", Bay Networks, Inc., IEE conf. 1997.

// update CRC for one bit of data
  function logic [31:0] CRC32_1(logic data, logic [31:0] fcs);
    int j;
    CRC32_1[0] = fcs[31] ^ data;
    for (j=1; j<=31; j++) begin
      case (j)
        1,2,4,5,7,8,10,11,12,16,22,23,26 : 
           CRC32_1[j] = fcs[j-1]^fcs[31]^data;
        default : CRC32_1[j] = fcs[j-1];
      endcase
    end
  endfunction : CRC32_1

// update CRC for a nibble worth of data
  function logic [31:0] CRC32(nibble data, logic [31:0] fcs);
    logic [31:0] fcs_tmp [0:2] = '{3{32'b0}};
    int i = 0;
    fcs_tmp[0] = CRC32_1(data[0], fcs);
    for (i=1; i<=3; i++) 
      if (i==3) CRC32 = CRC32_1(data[i], fcs_tmp[2]);
      else      fcs_tmp[i] = CRC32_1(data[i], fcs_tmp[i-1]);
  endfunction : CRC32

// reverse and complement crc signature
  function logic [31:0] complement_reverse(logic [31:0] crc);
    int i = 0;
    for (i=0; i<32; i++) 
      complement_reverse[i] = !crc[31-i];
  endfunction :  complement_reverse

// TX variables and processes
// ==========================

  // nibble buffers
  logic [31:0] TX_D_Word_r = 0;
  wire [15:0] TX_Word = {TXD, TX_D_Word_r[31:20]};
  wire [15:0] TX_RevWord = {TX_Word[7:0], TX_Word[15:8]};
  wire [31:0] TX_D_Word = {TXD, TX_D_Word_r[31:4]};

  logic past_TX_EN = 1'b0; // past value of TX_EN
  wire rose_TX_EN = !past_TX_EN && TX_EN; 
  wire fell_TX_EN = past_TX_EN && !TX_EN; 

   // nibble counters, Frame byte counters bits [15:1]
  length_type TX_NibbleCnt = 0;

  // frame size for comparison when TX_EN deasserted
  logic [15:0] TX_FrameSize = 0;
                               
  logic [31:0] TX_Fcs = 32'hffffffff; // accumulate CRC

  // flags for rreporting an error detected by an assertion to TB
  // output port
  // the bits are set in the action block and reset at the end of a frame. 
  // interframe errors are reported from the end of the preceding 
  // frame

  task TX_SetFrameError(input mii_sva_tx_error_type i);
    TX_FrameError = i | TX_FrameError;
  endtask : TX_SetFrameError

  task TX_SetFrameCover(input mii_sva_tx_cover_type i);
    TX_FrameCover = i | TX_FrameCover;
  endtask : TX_SetFrameCover

  // TX MAC variables (back off delay calculations)

  bit [4:0] TX_BackOffState  = 0;
  bit TX_Collision           = 0;
  int TX_BackOffDelay        = 0;

  // sampling clock domain
  clocking txc @(posedge TX_CLK);
    // By default input #1step
    input TX_EN, TX_ER, TXD, COL, CRS;
    input rose_TX_EN, fell_TX_EN;
    input TX_Word, TX_RevWord, TX_D_Word;
  endclocking

// Boolean markers of positions in a frame

  wire TX_SdfValid = (TX_Word[15:8] == {SdfH, SdfL}) &&
                     (TX_NibbleCnt == 0) ;
  wire TX_DestAddrValid = (TX_NibbleCnt == 16'd12);
  wire TX_SrcAddrValid = (TX_NibbleCnt == 16'd24);
  wire TX_qTagValid = (TX_NibbleCnt == 16'd28) &&
                      (TX_RevWord == {qTagHigh, qTagLow});
  wire TX_NoTagLengthValid = (TX_NibbleCnt == 16'd28) &&
       (TX_RevWord <= maxValidFrame);
  wire TX_TagLengthValid = (TX_NibbleCnt == 16'd36) &&
       (TX_RevWord <= maxValidFrame);
  wire [15:0] TX_DataLength = TX_NoTagLengthValid || TX_TagLengthValid ? 
                 TX_RevWord : 
                 16'b0;
  wire TX_NoTagTypeValid = (TX_NibbleCnt == 16'd28) &&
       (TX_RevWord >= minTypeValue) && !TX_qTagValid;
  wire TX_TagTypeValid = (TX_NibbleCnt == 16'd36) &&
       (TX_RevWord >= minTypeValue);
  wire TX_EndOfFrame = !TX_EN && past_TX_EN;

// Update nibble count, FCS calculation, data word TX_D_Word_r

  always @(txc) begin : tx_frame_counts
    if (resetting || !txc.TX_EN) begin
      TX_NibbleCnt <= 0;
      TX_D_Word_r <= 0;
      past_TX_EN <= 0;
      TX_Fcs <= 32'hffffffff; // On rising edge of TX_EN?
    end 
    else begin
      TX_D_Word_r <= txc.TX_D_Word;
      past_TX_EN <= txc.TX_EN;
      if (TX_NoTagLengthValid || TX_TagLengthValid) 
        TX_FrameSize <= TX_RevWord ;
      if ((TX_Word[15:8] == {SdfH, SdfL}) ||
          (TX_NibbleCnt > 0)) begin
        TX_NibbleCnt <= TX_NibbleCnt + 1;
        if (TX_NibbleCnt > 8) TX_Fcs <= CRC32(TX_D_Word_r[3:0], TX_Fcs);
      end
    end
  end  : tx_frame_counts

// Initialize to 0 Error and Cover flags upon reset
`ifndef SYNTHESIS
  always @(posedge TX_CLK)
    if (resetting) begin
      TX_FrameError <= 0;
      TX_FrameCover <= 0;
    end
`endif

// MAC TX processes
// ================

// compute max backoff delay
  always @(txc) begin 
    if (!not_resetting) begin
      TX_BackOffState <= 0; // counts number of retransmissions
      TX_Collision <= 0; // collision occured in a frame
      TX_BackOffDelay <=0; // counter of interframe cycles
    end
    else begin
      // remember if COL occured until beginning of next frame
      if (txc.rose_TX_EN) TX_Collision <= 1'b0;
      if (txc.TX_EN && txc.COL) TX_Collision <= 1'b1;
      // maintain number of retransmissions
      // and count cycle in interframe gap
      if (txc.fell_TX_EN) begin
        if (TX_Collision && (TX_BackOffState < mii_TX_max_attempts))
             TX_BackOffState <=  TX_BackOffState + 1;
        else TX_BackOffState <= 0;
        TX_BackOffDelay <= 1;
      end else
        if (!txc.TX_EN) TX_BackOffDelay <= TX_BackOffDelay + 1;
    end
  end


// RX variables and processes
//===========================

  logic [31:0] RX_D_Word_r = 0;
  wire [15:0] RX_Word = {RXD, RX_D_Word_r[31:20]};
  wire [15:0] RX_RevWord = {RX_Word[7:0], RX_Word[15:8]};
  wire [31:0] RX_D_Word = {RXD, RX_D_Word_r[31:4]};

  logic past_RX_DV = 1'b0; // pas value of RX_DV 
  wire rose_RX_DV = !past_RX_DV && RX_DV;
  wire fell_RX_DV = past_RX_DV &&!RX_DV; 

  // nibble counters, Frame byte counters bits [15:1]
  length_type RX_NibbleCnt = 0;

  // frame size for comparison when RX_DV deasserted
  logic [15:0] RX_FrameSize = 0;
                               
  logic [31:0] RX_Fcs = 32'hffffffff; // accumulate CRC

  // flags for reporting an error detected by an assertion to TB
  // similar to TX

  task RX_SetFrameError(input mii_sva_rx_error_type i);
    RX_FrameError = i | RX_FrameError;
  endtask : RX_SetFrameError

  task RX_SetFrameCover(input mii_sva_rx_cover_type i);
    RX_FrameCover = i | RX_FrameCover;
  endtask : RX_SetFrameCover

  bit RX_Collision           = 0; // memorize collision occured

  // sampling clock domain
  clocking rxc @(posedge RX_CLK);
    // By default input #1step
    input RX_DV, RX_ER, RXD, COL, CRS;
    input rose_RX_DV, fell_RX_DV;
    input RX_Word, RX_RevWord, RX_D_Word;
  endclocking

// Boolean markers of positions in a frame

  wire RX_SdfValid = (RX_Word[15:8] == {SdfH, SdfL}) &&
                     (RX_NibbleCnt == 0) ;
  wire RX_DestAddrValid = (RX_NibbleCnt == 16'd12);
  wire RX_SrcAddrValid = (RX_NibbleCnt == 16'd24);
  wire RX_qTagValid = (RX_NibbleCnt == 16'd28) &&
                      (RX_RevWord == {qTagHigh, qTagLow});
  wire RX_NoTagLengthValid = (RX_NibbleCnt == 16'd28) &&
       (RX_RevWord <= maxValidFrame);
  wire RX_TagLengthValid = (RX_NibbleCnt == 16'd36) &&
       (RX_RevWord <= maxValidFrame);
  wire [15:0] RX_DataLength = RX_NoTagLengthValid || RX_TagLengthValid ? 
                 RX_RevWord : 
                 16'b0;
  wire RX_NoTagTypeValid = (RX_NibbleCnt == 16'd28) &&
       (RX_RevWord >= minTypeValue) && !RX_qTagValid;
  wire RX_TagTypeValid = (RX_NibbleCnt == 16'd36) &&
       (RX_RevWord >= minTypeValue);
  wire RX_EndOfFrame = !RX_DV && past_RX_DV;

// Update nibble count, FCS calculation, data word RX_D_Word_r

  always @(rxc) begin : rx_frame_counts
    if (resetting || !rxc.RX_DV) begin
      RX_NibbleCnt <= 0;
      RX_D_Word_r <= 0;
      past_RX_DV <= 0;
      RX_Fcs <= 32'hffffffff; 
      RX_Collision <= 0;
    end 
    else begin
      if (rose_RX_DV) RX_Collision <= 0;
      if (rxc.RX_DV && rxc.COL) RX_Collision <= 1;
      RX_D_Word_r <= rxc.RX_D_Word;
      past_RX_DV <= rxc.RX_DV;
      if (RX_NoTagLengthValid || RX_TagLengthValid) 
        RX_FrameSize <= RX_RevWord ;
      if ((RX_Word[15:8] == {SdfH, SdfL}) ||
          (RX_NibbleCnt > 0)) begin
        RX_NibbleCnt <= RX_NibbleCnt + 1;
        if (RX_NibbleCnt > 8) RX_Fcs <= CRC32(RX_D_Word_r[3:0], RX_Fcs); 
      end
    end
  end  : rx_frame_counts

// Initialize to 0 Error and Cover flags upon reset
`ifndef SYNTHESIS
  always @(posedge RX_CLK)
    if (resetting) begin
      RX_FrameError <= 0;
      RX_FrameCover <= 0;
    end
`endif


// MII Property definitions, TX and RX
// ===================================

  // as a rule, the last nibble received is taken directly from the
  // port, only previous nibbles and bytes are taken from
  // Nibble buffers if needed. 

`ifndef SVA_CHECKER_FORMAL
  property mii_1_p(miiEN, miiD, miiER);
    disable iff(resetting)
      ((miiEN ^ miiEN) == 0) &&
      ((miiD ^ miiD) == 0) &&
      ((miiER ^ miiER) == 0) &&
      ((COL ^ COL) == 0) &&
      ((CRS ^ CRS) == 0) ;
  endproperty :  mii_1_p
`endif

  // CRS remains asserted during collision condition COL. 
  property mii_2_p;
    disable iff (resetting || mii_FullDuplex) 
      !COL ##1 COL[*1:$] |-> CRS;
  endproperty : mii_2_p

// Example 3-12 Using Flags to Disable Other Assertions  
// TX_EN can become asserted only when CRS is deasserted
  property mii_TX_3_p; 
    disable iff (resetting || (|TX_FrameError) || mii_FullDuplex) 
      CRS && !RX_DV || $rose(RX_DV) ##4 1'b1 |-> !$rose(TX_EN);
  endproperty : mii_TX_3_p

  // TX_EN == 0 and TX_ER == 1 is a reserved state
  property mii_TX_4_p;
    disable iff (resetting)
      not (!TX_EN && TX_ER);
  endproperty : mii_TX_4_p

  // TX_EN is asserted with the first nibble of Preamble, 
  // there are 7 preamble bytes, followed by SDF.
  property mii_TX_5_p;
    disable iff (resetting || COL && !mii_FullDuplex)
      $rose(TX_EN) |-> (TXD == Preamble)[*14];
  endproperty : mii_TX_5_p

  property mii_TX_6_p; // First low order nibble of SDF
    disable iff (resetting || COL && !mii_FullDuplex) 
      $rose(TX_EN)  |-> ##14 TXD == SdfL;
  endproperty : mii_TX_6_p

  property mii_TX_7_p; // Second high order nibble of SDF
    disable iff (resetting || COL && !mii_FullDuplex) 
      $rose(TX_EN)  |-> ##15 TXD == SdfH;
  endproperty : mii_TX_7_p

  //  When there is no collision, between frame enable asserted 
  // and then deasserted there must be 2N nibbles
  property mii_8_p(SdfValid,EndOfFrame, NibbleCnt);
    disable iff (resetting || COL && !mii_FullDuplex)
      SdfValid ##1 EndOfFrame[->1] |-> NibbleCnt[0];
  endproperty : mii_8_p

  // CRS is asserted Kt = 2 clock cycles after TX_EN or RX_DV is 
  // asserted and remains asserted while TX_EN or RX_DV is asserted.
  property mii_9_p(miiEN, delay);
    disable iff (resetting || mii_FullDuplex)
      !miiEN ##1 miiEN |-> ##delay (CRS[*1:$]) ##1 !miiEN;
  endproperty : mii_9_p

  // During transmission when CRS is set then a 32 bit == 8 nibble jam
  // sequence is transmitted and then TX_EN is deasserted
  property mii_TX_10_p;
    disable iff (resetting || mii_FullDuplex)
      TX_EN  throughout (!COL ##1 COL)  |-> 
          TX_EN[*(2*jamSize):2*jamSize+4] ##1 !TX_EN; 
  endproperty : mii_TX_10_p

  // The resulting FCS when jamming must be invalid.
  // property is likely not be suitable for Magellan
  property mii_TX_11_p;
    disable iff (resetting || mii_FullDuplex)
      (TX_EN && (TX_NibbleCnt != 0) && TX_Collision) ##1 !TX_EN |-> 
          (TX_D_Word_r != complement_reverse(TX_Fcs));
  endproperty : mii_TX_11_p

  // When there is no collision and no TX_ER, transmitted FCS (the
  // last 4 octets of frame) must be correct.
  // property is likely not suitable for Magellan because the 
  // choice made regarding the frame length may collide with requiring 
  // !miiEN to happen and fcs be correct. 
  // The alternative is to make it depend on the length value of  
  // the frame rather than on miiEN... TBD
  property mii_12_p(miiEN, D_Word_r, Fcs_r);
    disable iff(resetting || TX_Collision  && !mii_FullDuplex)
      miiEN ##1 !miiEN |-> 
          (D_Word_r == complement_reverse(Fcs_r));
  endproperty : mii_12_p

  // Late collision happened - after 1 slot time 
  // (minFrameSize = 64 octets = 128 nibbles have been transmitted)
  // (including preamble and sdf??)
  property mii_13_p(NibbleCnt, miiEN);
    disable iff(resetting  || mii_FullDuplex)
      (NibbleCnt > minFrameSize*2) && miiEN |-> !$rose(COL);
  endproperty : mii_13_p

  // Frame is at least minFrameSize = 64 octets (not including Preamble and SDF?)
  // That is, after 128 nibbles after preamble and sdf TX_EN or RX_DV
  //  is still asserted on the next clock tick
  property mii_14_p(Collision, SdfValid, miiEN, NibbleCnt, value);
    disable iff(resetting || Collision && !mii_FullDuplex)
      SdfValid && miiEN ##1 (!miiEN)[->1] |-> (NibbleCnt > value);
  endproperty : mii_14_p

  // Frame is at most maxUntaggedFrameSize = 1518 octets w/o tag (b) 
  // and maxFrameSize = 1522 (a) with tag
  // present  (not including Preamble and SDF)
  property mii_15_p(miiEN, qTagValid, qTagLengthValid, NibbleCnt, value);
    disable iff(resetting || COL && !mii_FullDuplex)
      qTagValid ##8 qTagLengthValid
         |-> 
      (miiEN && (NibbleCnt <= value))[*1:$] ##1 !miiEN;
  endproperty : mii_15_p

  property mii_16_p(miiEN, NoTagLengthValid, NibbleCnt, value);
    disable iff(resetting || COL && !mii_FullDuplex)
      NoTagLengthValid 
         |-> 
      (miiEN && (NibbleCnt <= value))[*1:$] ##1 !miiEN;
  endproperty : mii_16_p

  // LengthType field is aligned with TX_EN or RX_DV
  // if to be interpreted as length (a) when tag 
  // (b) when no tag present. This check is done only when the length is
  // greater than 64 without tag and 60 with the tag.
  // Otherwise the pad bytes complete to that length, 
  // checked by mii_14_p.

  property mii_17_p(miiEN, qTagValid, DataLength, 
                     FrameSize, NibbleCnt);
    disable iff(resetting || COL && !mii_FullDuplex)
      (qTagValid ##8 (DataLength > minFrameSize-4) ##1 (!miiEN[->1]))
        |-> 
      (({1'b0,NibbleCnt[15:1]} - 16'd17) == FrameSize);
  endproperty : mii_17_p

  property mii_18_p(miiEN, NoTagLengthValid, DataLength, 
                     FrameSize, NibbleCnt);
    disable iff(resetting || COL && !mii_FullDuplex)
      (NoTagLengthValid && (DataLength > minFrameSize)) ##1 (!miiEN[->1])
        |-> 
      (({1'b0,NibbleCnt[15:1]} - 16'd14) == FrameSize);
  endproperty : mii_18_p

  // While RX_DV is deasserted then false carrier can be
  // indicated by RX_ER asserted and RXD == 1110.  
  property mii_RX_20_p;
    disable iff (resetting) 
      !RX_DV && RX_ER |-> RXD == 4'b1110;
  endproperty : mii_RX_20_p

  // RX_DV must be enabled no later than Start Frame Delimiter
  // (SFD). 
  // This means that 0 or more (up to 7) preamble octets could
  // also appear, followed by SFD.
  property mii_RX_7_p;
    disable iff (resetting || COL && !mii_FullDuplex) 
      !RX_DV ##1 RX_DV |->
          ##[2:16] (RX_Word[15:8] == {SdfH, SdfL});
  endproperty : mii_RX_7_p


// Shared MAC TX and RX property definition
//-----------------------------------------

  // The minimum interframe gap is 96 bit times, 
  // i.e., 24 clock ticks (with 4-bit data)
  property mac_19_p(miiEN);
    disable iff(resetting)
      miiEN ##1 !miiEN |-> !miiEN[*24];
  endproperty : mac_19_p

// MAC TX property definition
//---------------------------

  // When collision occurs during transmission, the backoff average
  // delay for next retransmission is at least that of the exponentially
  // increasing interval up to 10 retransmissions and then the upper
  // bound levels off at 1023 slot times. One slot time is 512 bits ==
  // 128 nibbles (clock ticks). This cannot be checked using assertions.
  // Used in assumptions, it constrains the retransmission to be 
  // within the exponentially increasing interval.

  property mac_TX_20_p;
    disable iff (resetting)
      !TX_EN ##1 (TX_Collision && TX_EN && (TX_BackOffState > 0))
        |->
      (TX_BackOffDelay <= (32'd128 * 
                            ((TX_BackOffState <= 5'd9) ?
                              ((32'd1 << TX_BackOffState) - 32'd1) :
                              32'd1023
                            )
                          )
      ) ;
  endproperty : mac_TX_20_p

`ifdef COVER_ON
// Coverage properties shared by TX and RX
// ---------------------------------------

//COL occurred within a frame : cover property
//  Cross coverage with symbol offset 0, 1, latest early, earliest late,
//  end of frame
//  Asserted ASAP (symbol == 0) - after SDF...?
//  Almost late (symbol = 63)
//  Earliest late (64)
//  Late
//  Also if asserted -1 symbols before end (and -n ??)

  // A COL occurred on a symbol
  // miiEN is TX_EN or RX_DV, 
  // cnt identifies position in frame based on nibble count
  // used everywhere except for last nibble
  property mii_cov_COL_p (miiEN, cnt);
    (not_resetting && miiEN && !mii_FullDuplex) throughout 
            ($rose(miiEN) ##0 (COL && cnt)[->1]);
  endproperty : mii_cov_COL_p 

  property mii_cov_COL_last_p (miiEN);
    ((not_resetting && miiEN && !mii_FullDuplex) throughout 
            ($rose(miiEN) ##0 COL[->1]))
      ##1 !miiEN ;
  endproperty : mii_cov_COL_last_p
 
  // exact min / max length packet detected, w/ and w/o tag 
  property frame_exact_length_p (miiEN, kind, cnt, frame_length);
    (not_resetting && (!COL || mii_FullDuplex)) throughout 
       (
        kind within ( $rose(miiEN) ##1 (miiEN)[*1:$] )
       )
     ##1 (!miiEN && (cnt == frame_length));
  endproperty : frame_exact_length_p

  // classification of frame length for each kind
  // untagged frame occurred, data or type kind, and
  // tagged frame occurred, data or type kind
  // covers successfully completed frames only (no COL)
  // miiEN is TX_EN or RX_DV
  // kind identifies the position of the desired frame kind

`ifndef SYNTHESIS
`ifdef IMPLEMENTED_CG

  covergroup length_cg(ref length_type cnt, 
                       input string cov_name, explanation);
    coverpoint cnt 
      {
        bins fr_length[] = {[1:1536]};
        bins fr_large = default; 
      }
    option.at_least = 1;
    option.per_instance = 1;
    option.name = cov_name;
    option.comment = explanation;
//    option.auto_bin_max = 100;
  endgroup : length_cg

  task automatic store_cnt(input length_type cnt, ref length_type v, 
                 ref length_cg cg_inst);
    v = cnt; cg_inst.sample;
  endtask : store_cnt

  property frame_length_p (miiEN, kind, cnt, frame_length, cg_inst);
    (not_resetting && (!COL || mii_FullDuplex)) throughout 
       (
        kind within ( $rose(miiEN) ##1 (miiEN)[*1:$] )
       )
     ##1 (!miiEN,  store_cnt(cnt, frame_length, cg_inst)) ;
  endproperty : frame_length_p

// cover group for interframe and back-off delay

  covergroup mac_TX_interframe_cg @(posedge TX_CLK);
    coverpoint TX_BackOffDelay iff (rose_TX_EN)
      { bins interframe_small[] = {[1:1024]};
        bins interframe_large = default;
      }
    coverpoint TX_BackOffState iff (rose_TX_EN); // 0 means no retry
//    cross TX_BackOffDelay, TX_BackOffState iff (rose_TX_EN);
    option.at_least = 1;
    option.per_instance = 1;
    option.name = "TX_Interframe gap";
    option.comment = "BackOffState==0 means no collision, normal interframe gap";
//    option.auto_bin_max = 100;
  endgroup : mac_TX_interframe_cg

`endif
`endif

  // min interframe gap
  property mac_min_interframe_p(miiEN);
    not_resetting throughout
      (miiEN ##1 !miiEN[*24] ##1 miiEN) ;
  endproperty :mac_min_interframe_p

`endif

// - Control frames : NOT SUPPORTED 
//  - Cover various pause interval - NOT SUPPORTED
//    - Interval was lengthened
//    - Interval was reset


// MII TX Assume, Assert and Cover
// =================================

`ifdef ASSERT_ON
  generate
    if(mii_TX_assume) begin : mii_TX_assumptions
`ifdef IMPLEMENTED_ASSUME
      always @(posedge TX_CLK) begin

       // Basic checks: no x or z value on any signal outside of reset
`ifndef SVA_CHECKER_FORMAL
        mii_TX_1: assume property (
                mii_1_p(TX_EN, TXD, TX_ER) );
`endif // SVA_CHECKER_FORMAL

        mii_TX_2: assume property(mii_2_p); 

        mii_TX_3: assume property(mii_TX_3_p); 

        mii_TX_4: assume property(mii_TX_4_p); 

        mii_TX_5: assume property(mii_TX_5_p); 

        mii_TX_6: assume property(mii_TX_6_p); 

        mii_TX_7: assume property(mii_TX_7_p); 

        mii_TX_8: assume property(mii_8_p(TX_SdfValid, TX_EndOfFrame, TX_NibbleCnt)); 

        mii_TX_9: assume property(mii_9_p(TX_EN, 2)); 

        mii_TX_10: assume property(mii_TX_10_p); 

        mii_TX_11: assume property(mii_TX_11_p); 

// not suitable as constraint, since it imposes it over past values
//        mii_TX_12: assume property(mii_12_p(TX_EN, TX_D_Word_r, TX_Fcs)); 

        mii_TX_13: assume property(mii_13_p(TX_NibbleCnt, TX_EN)); 

        mii_TX_14: assume property(mii_14_p(TX_Collision, TX_SdfValid, 
                                            TX_EN, TX_NibbleCnt, 
                                             (2*minFrameSize)) ); 

        mii_TX_15: assume property(
                      mii_11a_p(TX_EN, TX_qTagValid, TX_qTagLengthValid, 
                                TX_NibbleCnt, ( 2*maxFrameSize)) ); 

        mii_TX_16: assume property(
                      mii_16_p(TX_EN, TX_NoTagLengthValid, 
                                TX_NibbleCnt, (2*maxUntaggedFrameSize)) ); 

        mii_TX_17: assume property(
                      mii_17_p(TX_EN, TX_qTagValid, TX_DataLength, 
                                TX_FrameSize, TX_NibbleCnt) ); 

        mii_TX_18: assume property(
                      mii_18_p(TX_EN, TX_NoTagLengthValid, TX_DataLength, 
                                TX_FrameSize, TX_NibbleCnt) ); 
      end
`endif

    end : mii_TX_assumptions
    else begin : mii_TX_assertions
      always @(posedge TX_CLK) begin

`ifndef SVA_CHECKER_FORMAL
        mii_TX_1: assert property (
                mii_1_p(TX_EN, TXD, TX_ER) )
        else begin
          sva_checker_error ("TX signals x or z");
          TX_SetFrameError(MII_TX_x_z);
        end
`endif // SVA_CHECKER_FORMAL

        mii_TX_2: assert property(mii_2_p) 
        else begin
          sva_checker_error
            ("TC_CLK sampled CRS not asserted during collision condition");
          TX_SetFrameError(MII_TX_NO_CRS_W_COL);
        end

        mii_TX_3: assert property(mii_TX_3_p) 
        else begin
          sva_checker_error
            ("mii_TX_EN asserted when CRS is asserted");
          TX_SetFrameError(MII_TX_EN_ASSERT_WHEN_CRS);
        end

        mii_TX_4: assert property(mii_TX_4_p) 
        else begin
          sva_checker_error
            ("TX_EN == 0 and TX_ER == 1 is a reserved state");
          TX_SetFrameError(MII_TX_EN_ER_01);
        end

        mii_TX_5: assert property(mii_TX_5_p) 
        else begin
          sva_checker_error
            ("Bad Preamble octet");
          TX_SetFrameError(MII_TX_BAD_PREAMBLE);
        end

        mii_TX_6: assert property(mii_TX_6_p) 
        else begin
          sva_checker_error
            ("Bad low-order SDF nibble");
          TX_SetFrameError(MII_TX_BAD_LOW_SDF);
        end

        mii_TX_7: assert property(mii_TX_7_p) 
        else begin
          sva_checker_error
            ("Bad high-order SDF nibble");
          TX_SetFrameError(MII_TX_BAD_HIGH_SDF);
        end

        mii_TX_8: assert property(mii_8_p(TX_SdfValid, TX_EndOfFrame, TX_NibbleCnt)) 
        else begin
          sva_checker_error
            ("While TX_EN asserted there were 2N+1 nibbles");
          TX_SetFrameError(MII_TX_ODD_NIBBLES);
        end

        mii_TX_9: assert property(mii_9_p(TX_EN, 2)) 
        else begin
          sva_checker_error
            ("CRS not asserted 2 clock cycles after TX_EN");
          TX_SetFrameError(MII_TX_CRS_NOT_ASSERTED);
        end

        mii_TX_10: assert property(mii_TX_10_p) 
        else begin
          sva_checker_error
            ("TX When COL set then no 32 bit == 8 nibble jam sequence");
          TX_SetFrameError(MII_TX_NOT_A_JAM);
        end

        mii_TX_11: assert property(mii_TX_11_p) 
        else begin
          sva_checker_error
            ("TX FCS when jamming is not invalid");
          TX_SetFrameError(MII_TX_FCS_VALID_W_JAM);
        end

        mii_TX_12: assert property(mii_12_p(TX_EN, TX_D_Word_r, TX_Fcs)) 
        else begin
          sva_checker_error
            ("TX Transmitted FCS is incorrect");
          TX_SetFrameError(MII_TX_BAD_FCS);
        end

        mii_TX_13: assert property(mii_13_p(TX_NibbleCnt, TX_EN)) 
        else begin
          sva_checker_error
            ("TX Late collision occurred");
          TX_SetFrameError(MII_TX_LATE_COL);
        end

        mii_TX_14: assert property(mii_14_p(TX_Collision, TX_SdfValid,
                                            TX_EN, TX_NibbleCnt, 
                                            (2*minFrameSize)) ) 
        else begin
          sva_checker_error
            ("TX Frame is less than 64 octets");
          TX_SetFrameError(MII_TX_SHORT_FRAME);
        end

        mii_TX_15: assert property(
                      mii_15_p(TX_EN, TX_qTagValid, TX_TagLengthValid, 
                             TX_NibbleCnt, (2*maxFrameSize)) ) 
        else begin
          sva_checker_error
            ("TX Normal with qTag Frame is more than 1522 octets");
          TX_SetFrameError(MII_TX_TAGGED_FRAME_LONG);
        end

        mii_TX_16: assert property(
                      mii_16_p(TX_EN, TX_NoTagLengthValid, 
                             TX_NibbleCnt, (2*maxUntaggedFrameSize)) ) 
        else begin
          sva_checker_error
            ("TX Normal w/o qTag Frame is more than 1518 octets");
          TX_SetFrameError(MII_TX_NORMAL_FRAME_LONG);
        end

        mii_TX_17: assert property(
                      mii_17_p(TX_EN, TX_qTagValid, TX_DataLength, 
                                TX_FrameSize, TX_NibbleCnt) ) 
        else begin
          sva_checker_error
            ("TX Frame with qTag not matching Length value");
          TX_SetFrameError(MII_TX_TAGGED_BAD_LENGTH);
        end

        mii_TX_18: assert property(
                      mii_18_p(TX_EN, TX_NoTagLengthValid, TX_DataLength, 
                                TX_FrameSize, TX_NibbleCnt) ) 
        else begin
          sva_checker_error
            ("TX Normal Frame not matching Length value");
          TX_SetFrameError(MII_TX_NORMAL_BAD_LENGTH);
        end

      end
    end : mii_TX_assertions
  endgenerate

`endif // ASSERT_ON

// MII TX Covers
// -------------

`ifdef COVER_ON
        // TX Coverage statements, valid only 
        // when there is no failure of an assertion
        // -------------------
`ifndef SYNTHESIS
`ifdef IMPLEMENTED_CG

// Example 3-37 Coverage of Packet Length Using a covergroup and a sequence
        // classification of frame length for each kind
        // untagged frame occurred, data or type kind

      length_type TX_UntaggedFrameLength = 0;
      length_cg mii_TX_untagged_frame_length = new (
                             TX_UntaggedFrameLength, 
                             "mii_TX_untagged_frame_length", 
                             "coverage of TX untagged frame lengths");

        // tagged frame occurred, data or type kind
        length_type TX_TaggedFrameLength = 0;
        length_cg mii_TX_tagged_frame_length = new (
                             TX_TaggedFrameLength, 
                             "mii_TX_tagged_frame_length", 
                             "coverage of TX tagged frame lengths");

`endif
`endif

      always @(posedge TX_CLK) begin

        // A COL occurred on a symbol

        // Asserted ASAP (symbol == 0) - after SDF
        mii_TX_1COV: cover property (
          mii_cov_COL_p (TX_EN, $past(TX_SdfValid)) )
        TX_SetFrameCover(MII_TX_COL_ON_SYMBOL_0);

        // Almost late (symbol = 63)
        mii_TX_2COV: cover property (
          mii_cov_COL_p (TX_EN, (TX_NibbleCnt == 63)) )
        TX_SetFrameCover(MII_TX_COL_ALMOST_LATE);

        // Earliest late (64)
        mii_TX_3COV: cover property (
          mii_cov_COL_p (TX_EN, (TX_NibbleCnt == 64)) )
        TX_SetFrameCover(MII_TX_COL_EARLIEST_LATE);

        // Late
        mii_TX_4COV: cover property (
          mii_cov_COL_p (TX_EN, (TX_NibbleCnt > 64)) )
        TX_SetFrameCover(MII_TX_COL_LATE);

        // Also if asserted -1 symbols before end
        mii_TX_5COV: cover property (
          mii_cov_COL_last_p (TX_EN) )
        TX_SetFrameCover(MII_TX_COL_LAST);

`ifndef SYNTHESIS
`ifdef IMPLEMENTED_CG

        mii_TX_6COV: cover property (
          frame_length_p (TX_EN, TX_NoTagLengthValid, 
                          TX_NibbleCnt,  TX_UntaggedFrameLength,
                          mii_TX_untagged_frame_length ) )
        begin
          TX_SetFrameCover(MII_TX_UNTAGGED_FRAME);
        end

        mii_TX_7COV: cover property (
          frame_length_p (TX_EN, TX_qTagValid, 
                          TX_NibbleCnt, TX_TaggedFrameLength,
                          mii_TX_tagged_frame_length ) )
        begin
          TX_SetFrameCover(MII_TX_TAGGED_FRAME);
        end

`endif
`endif

       // detect TX_ER asserted during a frame
        mii_TX_8COV: cover property ( 
               !TX_EN ##1 (TX_EN[*1:$]) ##0 TX_ER )
           TX_SetFrameCover(MII_TX_ER_DETECTED);

      // detect reset during a frame
        mii_TX_9COV: cover property ( 
               !TX_EN ##1 (TX_EN[*1:$]) ##0 resetting )
           TX_SetFrameCover(MII_TX_RESET_DETECTED);
      end
`endif // COVER_ON

// MAC TX assume, assert and cover
// ===============================

  // When collision occurs during transmission, the backoff
  // delay for next retransmission in within the exponentially
  // increasing interval up to 10 retransmissions and then the upper
  // bound levels off at 1023 slot times. One slot time is 512 bits ==
  // 128 nibbles (clock ticks).

`ifdef ASSERT_ON
  generate
    if(mii_TX_assume) begin : mac_TX_assume_interframe
`ifdef IMPLEMENTED_ASSUME
      always @(posedge TX_CLK) begin

        mac_TX_19: assume property(mac_19_p(TX_EN));

        mac_TX_20: assume property(mac_TX_20_p);
      end
`endif
    end : mac_TX_assume_interframe
    else begin : mac_TX_assert_interframe
      always @(posedge TX_CLK) begin

        mac_TX_19: assert property(mac_19_p(TX_EN)) 
        else begin
          sva_checker_error
            ("TX Interframe gap is less than 96 bit times");
          TX_SetFrameError(MAC_TX_SHORT_INTERFR_GAP);
        end

/* not useful as assertion
        mii_TX_20: assert property(mac_TX_20_p) 
        else begin
          sva_checker_error
            ("Back_off delay is greater than max limit");
          TX_SetFrameError(MAC_TX_BIG_RETRANS_GAP);
        end
*/
      end
    end : mac_TX_assert_interframe
  endgenerate
`endif

// MAC TX Coverage
// ---------------

`ifdef COVER_ON

`ifndef SYNTHESIS
`ifdef IMPLEMENTED_CG

  // sample interframe gap length and also the back-off state
  // and their cross product
  // bins with TX_BackOffState == 0 indicate normal interframe gap
  // TX_BackOffState > 0 indicates the retransmission number
  // together with the back-off delay

    mac_TX_interframe_cg mac_TX_interframe = new ();

`endif
`endif

    always @(posedge TX_CLK) begin : tx_cover

        // The minimum interframe gap is 96 bit times, 
        // i.e., 24 clock ticks (with 4-bit data)

        mii_TX_8COV: cover property (mac_min_interframe_p(TX_EN))
          TX_SetFrameCover(MII_TX_MIN_INTERFRAME);
    end : tx_cover

`endif // COVER_ON


// MII RX Assume, Assert and Cover
//================================

`ifdef ASSERT_ON

// Example 3-57 Selection of Assume or Assert in MII/MAC Checker
  generate

    if(mii_RX_assume) begin : mii_RX_assumptions

`ifdef IMPLEMENTED_ASSUME
      always @(posedge RX_CLK) begin
       // Basic checks: no x or z value on any signal outside of reset
`ifndef SVA_CHECKER_FORMAL
        mii_RX_1: assume property (
                mii_1_p(RX_DV, RXD, RX_ER) );
`endif

        mii_RX_2: assume property(mii_2_p); 

        mii_RX_7: assume property(mii_RX_7_p); 

        mii_RX_8: assume property(mii_8_p(RX_SdfValid, RX_EndOfFrame, RX_NibbleCnt)); 

        mii_RX_9: assume property(mii_9_p(RX_DV, 2)); 

// not suitable as a constraint since it applies it over past values
//        mii_RX_12: assume property(mii_12_p(RX_DV, RX_D_Word_r, RX_Fcs)); 

        mii_RX_13: assume property(mii_13_p(RX_NibbleCnt, RX_DV));


        mii_RX_14: assume property(mii_14_p(RX_Collision, RX_SdfValid, 
                                            RX_DV, RX_NibbleCnt, 
                                            2*minFrameSize)); 

        mii_RX_15: assume property(
                      mii_15_p(RX_DV, RX_qTagValid, RX_qTagLengthValid, 
                                RX_NibbleCnt, 2*maxFrameSize) ); 

        mii_RX_16: assume property(
                      mii_16_p(RX_DV, RX_NoTagLengthValid, 
                                RX_NibbleCnt, 2*maxUntaggedFrameSize) ); 

        mii_RX_17: assume property(
                      mii_17_p(RX_DV, RX_qTagValid, RX_DataLength, 
                                RX_FrameSize, RX_NibbleCnt) );

        mii_RX_18: assume property(
                      mii_18_p(RX_DV, RX_NoTagLengthValid, RX_DataLength, 
                                RX_FrameSize, RX_NibbleCnt) ); 

        mii_RX_20: assume property(mii_RX_20_p);  
      end
`endif

    end : mii_RX_assumptions
    else begin : mii_RX_assertions
      always @(posedge RX_CLK) begin

`ifndef SVA_CHECKER_FORMAL
        mii_RX_1: assert property (
                mii_1_p(RX_DV, RXD, RX_ER) )
        else begin
          RX_SetFrameError(MII_RX_BAD_OR_NO_SDF);
          sva_checker_error
            ("RX signals x or z");
        end
`endif

        mii_RX_2: assert property(mii_2_p) 
        else begin
          sva_checker_error
            ("RX_CLK sampled CRS not asserted during collision condition");
          RX_SetFrameError(MII_RX_CRS_NOT_W_COL);
        end

       mii_RX_7: assert property(mii_RX_7_p) 
        else begin
          sva_checker_error
            ("RX Bad or no SDF");
          RX_SetFrameError(MII_RX_BAD_OR_NO_SDF);
        end

        mii_RX_8: assert property(mii_8_p(RX_SdfValid, RX_EndOfFrame, RX_NibbleCnt)) 
        else begin
          sva_checker_error
            ("RX While RX_DV asserted there were 2N+1 nibbles");
          RX_SetFrameError(MII_RX_ODD_NIBBLES);
        end

        mii_RX_9: assert property(mii_9_p(RX_DV, 2)) 
        else begin
          sva_checker_error
            ("CRS not asserted 2 clock cycles after RX_DV");
          RX_SetFrameError(MII_RX_CRS_NOT_ASSERTED);
        end

        mii_RX_12: assert property(mii_12_p(RX_DV, RX_D_Word_r, RX_Fcs)) 
        else begin
          sva_checker_error
            ("RX Received FCS is incorrect");
          RX_SetFrameError(MII_RX_BAD_FCS);
        end

        mii_RX_13: assert property(mii_13_p(RX_NibbleCnt, RX_DV)) 
        else begin
          sva_checker_error
            ("RX Late collision occurred");
          RX_SetFrameError(MII_RX_LATE_COL);
        end

        mii_RX_14: assert property(mii_14_p(RX_Collision, RX_SdfValid, 
                                            RX_DV, RX_NibbleCnt, 
                                            2*minFrameSize) ) 
        else begin
          sva_checker_error
            ("RX Frame is less than minFrameSize octets");
          RX_SetFrameError(MII_RX_SHORT_FRAME);
        end

        mii_RX_15: assert property(
                      mii_15_p(RX_DV, RX_qTagValid, RX_TagLengthValid, 
                                RX_NibbleCnt, 2*maxFrameSize) ) 
        else begin
          sva_checker_error
            ("RX Normal with qTag Frame is more than maxFrameSize octets");
          RX_SetFrameError(MII_RX_TAGGED_FRAME_LONG);
        end

        mii_RX_16: assert property(
                      mii_16_p(RX_DV, RX_NoTagLengthValid, 
                                RX_NibbleCnt, 2*maxUntaggedFrameSize) ) 
        else begin
          sva_checker_error
            ("RX Normal w/o qTag Frame is more than maxUntaggedFrameSize octets");
          RX_SetFrameError(MII_RX_NORMAL_FRAME_LONG);
        end

        mii_RX_17: assert property(
                      mii_17_p(RX_DV, RX_qTagValid, RX_DataLength, 
                                RX_FrameSize, RX_NibbleCnt) ) 
        else begin
          sva_checker_error
            ("RX Frame with qTag not matching Length value");
          RX_SetFrameError(MII_RX_TAGGED_BAD_LENGTH);
        end

        mii_RX_18: assert property(
                      mii_18_p(RX_DV, RX_NoTagLengthValid, RX_DataLength, 
                                RX_FrameSize, RX_NibbleCnt) ) 
        else begin
          sva_checker_error
            ("RX Normal Frame not matching Length value");
          RX_SetFrameError(MII_RX_NORMAL_BAD_LENGTH);
        end

        mii_RX_20: assert property(mii_RX_20_p) 
        else begin
          sva_checker_error
            ("RX_DV == 0 and RX_ER == 1 with other than RXD == 1110");
          RX_SetFrameError(MII_RX_DV_ER_D_01_NOT1110);
        end

      end
    end : mii_RX_assertions
  endgenerate
`endif // ASSERT_ON

// MII RX Cover statements
// -----------------------

`ifdef COVER_ON

`ifndef SYNTHESIS
`ifdef IMPLEMENTED_CG

      // classification of frame length for each kind
      // untagged frame occurred, data or type kind
      length_type RX_UntaggedFrameLength = 0;
      length_cg mii_RX_untagged_frame_length = new (
                             RX_UntaggedFrameLength, 
                             "mii_RX_untagged_frame_length", 
                             "coverage of RX untagged frame lengths");
      // tagged frame occurred, data or type kind
      length_type RX_TaggedFrameLength = 0;
      length_cg mii_RX_tagged_frame_length = new (
                             RX_TaggedFrameLength, 
                             "mii_RX_tagged_frame_length", 
                             "coverage of RX tagged frame lengths");

`endif
`endif

      // RX Coverage statements, valid only 
      // when there is no failure of an assertion

      always @(posedge RX_CLK) begin

        // A COL occurred on a symbol
        // Asserted ASAP (symbol == 0) - after SDF
        mii_RX_1COV: cover property (
          mii_cov_COL_p (RX_DV, $past(RX_SdfValid)) )
        RX_SetFrameCover(MII_RX_COL_ON_SYMBOL_0);

        // Almost late (symbol = 63)
        mii_RX_2COV: cover property (
          mii_cov_COL_p (RX_DV, (RX_NibbleCnt == 63)) )
        RX_SetFrameCover(MII_RX_COL_ALMOST_LATE);

        // Earliest late (64)
        mii_RX_3COV: cover property (
          mii_cov_COL_p (RX_DV, (RX_NibbleCnt == 64)) )
        RX_SetFrameCover(MII_RX_COL_EARLIEST_LATE);

        // Late
        mii_RX_4COV: cover property (
          mii_cov_COL_p (RX_DV, (RX_NibbleCnt > 64)) )
        RX_SetFrameCover(MII_RX_COL_LATE);

        // Also if asserted -1 symbols before end
        mii_RX_5COV: cover property (
          mii_cov_COL_last_p (RX_DV) )
        RX_SetFrameCover(MII_RX_COL_LAST);

`ifdef IMPLEMENTED_CG

        mii_RX_6COV: cover property (
          frame_length_p (RX_DV, RX_NoTagLengthValid, 
                          RX_NibbleCnt, RX_UntaggedFrameLength,
                          mii_RX_untagged_frame_length) )
        begin
          RX_SetFrameCover(MII_RX_UNTAGGED_FRAME);
        end

        mii_RX_7COV: cover property (
          frame_length_p (RX_DV, RX_qTagValid, 
                          RX_NibbleCnt, RX_TaggedFrameLength,
                          mii_RX_tagged_frame_length) )
        begin
          RX_SetFrameCover(MII_RX_TAGGED_FRAME);
        end

`endif

       // detect RX_ER asserted during a frame
        mii_RX_8COV: cover property ( 
           not_resetting throughout
             ( !RX_DV ##1 (RX_DV[*1:$]) ##0 RX_ER ))
           RX_SetFrameCover(MII_RX_ER_DETECTED);

      // detect resetting during a frame
        mii_RX_9COV: cover property ( 
               !RX_DV ##1 (RX_DV[*1:$]) ##0 resetting )
           RX_SetFrameCover(MII_RX_RESET_DETECTED);

      // false carrier detected
        mii_RX_13COV: cover property (
           not_resetting && 
             (!RX_DV && RX_ER && (RXD == 4'b1110)) )
           RX_SetFrameCover(MII_RX_FALSE_CARRIER);           
     end

`endif // COVER_ON

// MAC RX assume, assert and cover
// ===============================

`ifdef ASSERT_ON
  generate
    if(mii_RX_assume) begin : mac_RX_assume_interframe

`ifdef IMPLEMENTED_ASSUME
      always @(posedge RX_CLK) begin
        mac_RX_19: assume property(mac_19_p(RX_DV));
      end
`endif

    end : mac_RX_assume_interframe
    else begin : mac_RX_assert_interframe
      always @(posedge RX_CLK) begin

        mac_RX_19: assert property(mac_19_p(RX_DV)) 
        else begin
          sva_checker_error
            ("RX Interframe gap is less than 96 bit times");
          RX_SetFrameError(MII_RX_SHORT_INTERFR_GAP);
        end

      end
    end : mac_RX_assert_interframe
  endgenerate

`endif // ASSERT_ON

`ifdef COVER_ON
  always @(posedge RX_CLK)
    mac_RX_2COV: cover property (mac_min_interframe_p(RX_DV));
`endif

endinterface : mii_sva_checker

`endif
