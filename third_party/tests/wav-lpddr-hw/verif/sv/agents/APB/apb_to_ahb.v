/*********************************************************************************
Copyright (c) 2021 Wavious LLC

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.

*********************************************************************************/

//`timescale 1ns/1ps

module apb_to_ahb # (
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
)(
    input  wire                     pclk,
    input  wire                     presetn,
    input  wire                     psel,
    input  wire                     penable,
    input  wire                     pwrite,
    input  wire [DATA_WIDTH-1:0]    pwdata,
    input  wire [ADDR_WIDTH-1:0]    paddr,
    output wire [DATA_WIDTH-1:0]    prdata,
    output reg                      pready,
    output reg                      pslverr,

    output wire                     hsel,
    output wire [ADDR_WIDTH-1:0]    haddr,
    output wire                     hwrite,
    output wire [2:0]               hsize,
    output wire [2:0]               hburst,
    output wire [3:0]               hprot,
    output wire [1:0]               htrans,
    output wire                     hmastlock,
    output wire [DATA_WIDTH-1:0]    hwdata,
    output wire                     hready,
    input  wire                     hreadyout,
    input  wire [DATA_WIDTH-1:0]    hrdata,
    input  wire                     hresp,

    input  wire                     core_scan_asyncrst_ctrl
);

// wire error_in;
// reg error;
// wire hready_seen_in;
// reg hready_seen;
// reg hwrite_seen;
// wire hwrite_seen_in;
//
//  // no need to pipeline, APB accesses can be mapped on to AHB accesses cycle for cycle
//  // no protection information though
//  // error is 2 cycles for AHB though but ready is 0 for first cycle so it can be mapped directly
//  // need the hresp to be 1 for 2 cycles though, first one hreadyout is 0 second it is 1
//
//  always @(posedge pclk or negedge presetn) begin
//    if (~presetn) begin
//      error <= 1'b0;
//      hready_seen <= 1'b0;
//      hwrite_seen <= 1'b0;
//    end else begin
//      error <= error_in;
//      hready_seen <= hready_seen_in;
//      hwrite_seen <= hwrite_seen_in;
//    end
//  end
//  assign hready_seen_in = hready_seen ? (pready ? 1'b0 : hready_seen) : hreadyout & psel;
//  assign hwrite_seen_in = hwrite_seen ? (pready ? 1'b0 : hwrite_seen) : hreadyout & pwrite & psel;
//  assign error_in = penable & psel & hresp & ~hreadyout ? 1'b1 : (hreadyout ? 1'b0 : error);
    //assign hwrite    = pwrite & ~hwrite_seen;
    //assign pready    = hreadyout & hready_seen & psel & penable;
    //assign pslverr   = error & hresp & psel & penable & hreadyout;

    reg  [1:0]      data_naddr_phase;
    reg  [1:0]      data_naddr_phase_in;

    reg             pready_in;
    reg             pslverr_in;
    reg  [31:0]     hrdata_1;    ///HARI added - Delayed rdata

    always @(posedge pclk or negedge presetn) begin
        if (~presetn) begin
          hrdata_1   <= 32'h0;
        end
        else begin
         hrdata_1   <= hrdata;
        end
    end
    always @(posedge pclk or negedge presetn) begin
      if (~presetn) begin
        data_naddr_phase      <= 2'b00;
        pready                <= 1'b0;
        pslverr               <= 1'b0;
      end else begin
        data_naddr_phase      <= psel ? data_naddr_phase_in : 1'b0;
        pready    <= hreadyout & psel & penable;
        //pready                <= pready_in;
        pready                <= pready_in;
        pslverr               <= pslverr_in;
      end
    end

    always @(*) begin
      data_naddr_phase_in         = data_naddr_phase;
      pready_in                   = 1'b0;
      pslverr_in                  = 1'b0;
      case (data_naddr_phase)
        2'b00 : begin  // IDLE -> SETUP / ADDRESS PHASE
          if (psel & hreadyout) begin
            data_naddr_phase_in   = 2'b01;
          end else begin
            data_naddr_phase_in   = 2'b00;
          end
        end
        2'b01 : begin  // ACCESS / DATA PHASE
          if (penable & (hreadyout | hresp)) begin
            data_naddr_phase_in   = 2'b11;
            pready_in             = 1'b1;
            pslverr_in            = hresp;
          end else begin
            data_naddr_phase_in   = 2'b01;
          end
        end
        2'b11 : begin  // APB TERMINATE PHASE
          if (~penable) begin
            data_naddr_phase_in   = 2'b00;
          end else begin
            data_naddr_phase_in   = 2'b11;
          end
        end
        default : begin
          data_naddr_phase_in     = 2'b00;
        end
      endcase
    end

    //assign data_naddr_phase_in = ~psel ? 1'b0
    //                                   : data_naddr_phase ? penable & (hreadyout | hresp) ? 1'b0 : 1'b1
    //                                                      : psel & hreadyout ? 1'b1 : 1'b0;

    generate
      if (DATA_WIDTH < 9) begin : gen_byte
        assign hsize = 3'b000; // 32 bits always
      end else if (DATA_WIDTH < 17) begin : gen_half_word
        assign hsize = 3'b001; // 32 bits always
      end else begin : gen_word
        assign hsize = 3'b010; // 32 bits always
      end
    endgenerate

    assign hsel      = psel & hreadyout & ~data_naddr_phase[0];
    assign haddr     = paddr;
    assign hwrite    = psel & pwrite & ~data_naddr_phase[0];
    assign hburst    = 3'b000;  // APB does not burst
    assign hprot     = 4'b0011; //  uncacheable, unbufferable, privileged, data access
    assign htrans    = 2'b10;   //  nonsequential
    assign hmastlock = 1'b0;
    assign hwdata    = pwdata;
    assign hready    = hreadyout;

    assign prdata    = hrdata_1;
    //assign pready    = psel & penable & (hreadyout | hresp) & data_naddr_phase[0];
    //assign pslverr   = psel & penable & hresp & data_naddr_phase[0];

endmodule
