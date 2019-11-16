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


`ifndef VMM_HW_DATA_WIDTH
`define VMM_HW_DATA_WIDTH 1024
`endif

`ifdef VMM_HW_RTL__SV
`else
`define VMM_HW_RTL__SV


//
// Select the target architecture
//
`undef VMM_HW_ARCH

`ifdef VMM_HW_ARCH_SCEMI
   // Throw a syntax error if more than one architecture was selected
   `ifdef VMM_HW_ARCH
      `VMM_HW_More_than_one_HW_platform_architecture_selected
   `endif
   `define VMM_HW_ARCH
`endif


`ifdef VMM_HW_ARCH_NULL
   // Throw a syntax error if more than one architecture was selected
   `ifdef VMM_HW_ARCH
      `VMM_HW_More_than_one_HW_platform_architecture_selected
   `endif
   `include "vmm.sv"
   `define VMM_HW_ARCH
`endif


// Throw a syntax error if no architecture was selected
`ifdef VMM_HW_ARCH
`else
   `VMM_HW_No_HW_platform_architecture_selected
`endif


// Include the DUT if mapping to hardware platform (ie. synthesis)
// or using the NULL architecture
`ifdef VMM_HW_SYNTHESIS_ON
   `define VMM_HW_INCL_DUT
`endif
`ifdef VMM_HW_ARCH_NULL
   `define VMM_HW_INCL_DUT
`endif


//
//------------------------------------------------------------------
//


`ifdef VMM_HW_SYNTHESIS_ON
`else
interface vmm_hw_in_if_itf(input  logic                          rx_rdy,
                           output logic                          tx_rdy,
                           output logic [`VMM_HW_DATA_WIDTH-1:0] msg,
                           input  logic                          uclk,
                           input  logic                          urst,
                           input  int                            width,
                           input  bit [1024*8-1:0]               path);

`ifdef VMM_HW_ARCH_NULL

`ifdef INCA
   string inst = $psprintf("%s", path);
`else
`ifdef NO_STRING_CAST
   string inst = path;
`else
   string inst = string'(path);
`endif
`endif

   vmm_log log = new("vmm_hw_in_if", inst);
   bit in_use = 0;

   clocking ck @(posedge uclk);
      input rx_rdy;
   endclocking
`endif

endinterface
`endif


`ifndef VMM_SVDOC
module vmm_hw_in_if(rx_rdy, tx_rdy, msg, uclk, urst);

   parameter width = 1;

   input              rx_rdy;
   output             tx_rdy;
   output [width-1:0] msg;
   input              uclk;
   input              urst;

`ifdef VMM_HW_SYNTHESIS_ON

   `ifdef VMM_HW_ARCH_SCEMI
      SceMiMessageInPort #(width) scemi(rx_rdy, tx_rdy, msg);
   `endif


`else

   reg [1024*8-1:0] path = `vmm_vector_sformatf("%m");

   initial
   begin
      if (vmm_hw.max_data_width < width) begin
         vmm_hw.max_data_width = width;
      end
   end

   wire [`VMM_HW_DATA_WIDTH-1:0] msg_i;
   assign msg = msg_i;

   vmm_hw_in_if_itf vitf(rx_rdy, tx_rdy, msg_i, uclk, urst, width, path);

`endif

endmodule
`endif


//
//------------------------------------------------------------------
//  
`ifdef VMM_HW_SYNTHESIS_ON
`else
interface vmm_hw_out_if_itf(input  logic                          tx_rdy,
                            output logic                          rx_rdy,
                            input  logic [`VMM_HW_DATA_WIDTH-1:0] msg,
                            input  logic                          uclk,
                            input  logic                          urst,
                            input  int                            width,
                            input  bit [1024*8-1:0]               path);

`ifdef VMM_HW_ARCH_NULL
`ifdef INCA
   string inst = $psprintf("%s",path);
`else
`ifdef NO_STRING_CAST
   string inst = path;
`else
   string inst = string'(path);
`endif
`endif

   vmm_log log = new("vmm_hw_out_if", inst);
   bit in_use = 0;

   clocking ck @(posedge uclk);
      input tx_rdy;
      input msg;
   endclocking
`endif


endinterface
`endif


`ifndef VMM_SVDOC
module vmm_hw_out_if(tx_rdy, rx_rdy, msg, uclk, urst);
   parameter width = 1;
   parameter pri = 10;

   input               tx_rdy;
   output              rx_rdy;
   input  [width-1:0]  msg;
   input               uclk;
   input               urst;


`ifdef VMM_HW_SYNTHESIS_ON

   `ifdef VMM_HW_ARCH_SCEMI
      SceMiMessageOutPort #(width, pri) scemi(tx_rdy, rx_rdy, msg);
   `endif


`else

   reg [1024*8-1:0] path = `vmm_vector_sformatf("%m");

   initial
   begin
      if (vmm_hw.max_data_width < width) begin
         vmm_hw.max_data_width = width;
      end
   end

   wire [`VMM_HW_DATA_WIDTH-1:0] msg_i = msg;

   vmm_hw_out_if_itf vitf(tx_rdy, rx_rdy, msg_i, uclk, urst, width, path);

`endif

endmodule
`endif



//
//------------------------------------------------------------------
//  
`ifdef VMM_HW_SYNTHESIS_ON
`else
interface vmm_hw_clock_control_itf(input  logic            uclk,
                                   input  logic            urst,
                                   input  logic            rdy_for_cclk,
                                   output logic            cclk_en,
                                   input  logic            rdy_for_cclk_neg,
                                   output logic            cclk_neg_en,
                                   input  bit [1024*8-1:0] path,
                                   input  int              clock_num);

`ifdef VMM_SVDOC
reg foo;
`endif

endinterface
`endif


`ifndef VMM_SVDOC
module vmm_hw_clock_control(uclk, urst,
                            rdy_for_cclk, cclk_en,
                            rdy_for_cclk_neg, cclk_neg_en);
   parameter clock_num = 1;

   output reg uclk;
   output reg urst;
   input  rdy_for_cclk;
   output cclk_en;
   input  rdy_for_cclk_neg;
   output cclk_neg_en;


`ifdef VMM_HW_SYNTHESIS_ON
   `ifdef VMM_HW_ARCH_SCEMI
      SceMiClockControl #(clock_num) scemi(uclk, urst,
                                           rdy_for_cclk, cclk_en,
                                           rdy_for_cclk_neg, cclk_neg_en);
   `endif


`else

   reg [1024*8-1:0] path = `vmm_vector_sformatf("%m");

`ifdef VMM_HW_ARCH_NULL
   // Make sure uclk and cclk are delta-cycle aligned
   always @(vmm_hw.uclk) uclk <= vmm_hw.uclk;
   always @(vmm_hw.urst) urst <= vmm_hw.urst;

   initial
   begin
      repeat (2) @ (posedge uclk);
      if (cclk_en === 1'bx || cclk_neg_en === 1'bx) begin
         $write("ERROR: clock controller %m is not associated with a clock source\n");
         $finish();
      end
   end
`endif

   vmm_hw_clock_control_itf vitf(uclk, urst,
                                 rdy_for_cclk, cclk_en,
                                 rdy_for_cclk_neg, cclk_neg_en,
                                 path, clock_num);

`endif

endmodule
`endif


//
//------------------------------------------------------------------
//  
`ifndef VMM_SVDOC
module vmm_hw();

int max_data_width = 0;

initial
begin
   #10;
   if (max_data_width > `VMM_HW_DATA_WIDTH) begin
      $write("ERROR: `VMM_HW_DATA_WIDTH must be set to %0d or greater instead of %0d\n",
             max_data_width, `VMM_HW_DATA_WIDTH);
      $finish();
   end
end


`ifdef VMM_HW_ARCH_NULL
reg uclk;
reg urst;
reg crst;
time stamp;

int reset_cycles = 8;

initial
begin
   stamp    = 0;
   uclk     = 0;

   #1; // Make sure 'urst' is asserted before clock rises
   forever begin
      #1 uclk = 1;
      stamp = stamp + 1;
      #1 uclk = 0;
   end
end

initial
begin
   urst = 0;
   crst = 0;
   #1; // To avoid race condition with 'always @(vmm_hw.urst)'
   urst = 1;
   repeat (5) @ (posedge uclk);
   crst <= 1'b1;
   repeat (5) @ (posedge uclk);
   urst <= 0;
   repeat (reset_cycles * 2) @ (posedge uclk);
   crst <= 1'b0;
end

`endif

endmodule
`endif


//
//------------------------------------------------------------------
//  
`ifdef VMM_HW_SYNTHESIS_ON
`else
interface vmm_hw_clock_itf(input int   clock_num,
                           input logic ck_en,
                           input logic ckn_en,
                           output int  no_pos,
                           output int  no_neg);
   string controller[$];
   logic  rdy_pos[$];
   logic  rdy_neg[$];

   function void why();
      if (controller.size() == 0) begin
         $write("Clock source %M does not have any associated controllers\n");
         return;
      end
      $write("State of controllers associated with %M:\n");
      $write("  Pos Neg :: Instance\n");
      foreach(controller[i]) begin
         $write("   %b   %b :: %s\n", rdy_pos[i], rdy_neg[i], controller[i]);
      end
   endfunction: why

   function int controller_size();
     return controller.size();
   endfunction
endinterface
`endif


`ifndef VMM_SVDOC
module vmm_hw_clock(cclk, crst, crstn);
   parameter clock_num         = 1;

   parameter ratio_numerator   = 1;
   parameter ratio_denominator = 1;
   parameter duty_hi           = 0;
   parameter duty_lo           = 100;
   parameter phase             = 0;
   parameter reset_cycles      = 8;

   output cclk;
   output crst, crstn;

`ifdef VMM_HW_SYNTHESIS_ON
`else
   bit ck_en;
   bit ckn_en;
   int no_pos;
   int no_neg;
`endif

`ifdef VMM_HW_ARCH_NULL
   assign crst  = vmm_hw.crst;
   assign crstn = ~vmm_hw.crst;

   wor no_posw;   // For Openvera
   wor no_negw;   // For Openvera

   reg cclk = 0;

   // Controlled clocks must run while ccrst is asserted
   assign ck_en  = (vmm_hw.urst === 1'b0) && (cclk == 1'b0) &&
                   ((no_pos == 0 && no_posw === 1'bz) || crst);
   assign ckn_en = (vmm_hw.urst === 1'b0) && (cclk == 1'b1) &&
                   ((no_neg == 0 && no_negw === 1'bz) || crst);

   initial
   begin
      if (vmm_hw.reset_cycles < reset_cycles) begin
         vmm_hw.reset_cycles = reset_cycles;
      end

      if (ratio_numerator != ratio_denominator) begin
         $write("WARNING: Unsupported ratio for clock source %M: %0d/%0d (must be 1/1)\n",
                ratio_numerator, ratio_denominator);
      end
      if (duty_hi != 0 && duty_lo != 0) begin
         $write("WARNING: Unsupported duty cycle for clock source %M: %0d/%0d (must be 0/x or x/0)\n",
                duty_hi, duty_lo);
      end
      if (phase != 0) begin
         $write("WARNING: Unsupported phase for clock source %M: %0d (must be 0)\n",
                phase);
      end
   end

   always @ (posedge vmm_hw.uclk)
   begin
      if (vmm_hw.urst) cclk <= 1'b0;
      else begin
         if (ck_en)  cclk <= 1'b1;
         if (ckn_en) cclk <= 1'b0;
      end
   end

`endif


`ifdef VMM_HW_SYNTHESIS_ON

   `ifdef VMM_HW_ARCH_SCEMI
      SceMiClockPort #(clock_num,
                       ratio_numerator, ratio_denominator,
                       duty_hi, duty_lo, phase, reset_cycles) scemi(cclk, crst);
   `endif


`else

   vmm_hw_clock_itf vitf(clock_num, ck_en, ckn_en, no_pos, no_neg);

`endif

endmodule
`endif

`endif // VMM_HW_RTL__SV
