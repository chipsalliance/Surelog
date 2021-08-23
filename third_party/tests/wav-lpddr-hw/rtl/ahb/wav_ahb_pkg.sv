
/*********************************************************************************
Copyright (c) 2021 Wavious LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*********************************************************************************/

`ifndef WAV_AHB_PKG
`define WAV_AHB_PKG

`timescale 1ps/1ps

package wav_ahb_pkg;

   parameter [2:0] AHB_SIZE_BYTE      = 3'b000;
   parameter [2:0] AHB_SIZE_HWORD     = 3'b001;
   parameter [2:0] AHB_SIZE_WORD      = 3'b010;
   parameter [2:0] AHB_SIZE_DWORD     = 3'b011;
   parameter [2:0] AHB_SIZE_BIT128    = 3'b100;
   parameter [2:0] AHB_SIZE_BIT256    = 3'b101;
   parameter [2:0] AHB_SIZE_BIT512    = 3'b110;

   parameter [2:0] AHB_BURST_SINGLE   = 3'b000;
   parameter [2:0] AHB_BURST_INCR     = 3'b001;
   parameter [2:0] AHB_BURST_INCR4    = 3'b011;
   parameter [2:0] AHB_BURST_INCR8    = 3'b101;
   parameter [2:0] AHB_BURST_INCR16   = 3'b111;

   parameter [1:0] AHB_TRANS_IDLE     = 2'b00;
   parameter [1:0] AHB_TRANS_BUSY     = 2'b01;
   parameter [1:0] AHB_TRANS_NONSEQ   = 2'b10;
   parameter [1:0] AHB_TRANS_SEQ      = 2'b11;

   parameter [1:0] AHB_RESP_OK        = 2'b00;
   parameter [1:0] AHB_RESP_ERROR     = 2'b01;
   parameter [1:0] AHB_RESP_RETRY     = 2'b10;
   parameter [1:0] AHB_RESP_SPLIT     = 2'b11;

endpackage : wav_ahb_pkg
`endif // WAV_AHB_PKG
