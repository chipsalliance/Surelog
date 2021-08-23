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

module mvp_pll_clk_control(
  input  wire     core_scan_asyncrst_ctrl,                   
  input  wire     core_scan_clk,                             
  input  wire     core_scan_mode,   
  
  input  wire     hclk,
  output wire     hclk_scan,
  input  wire     hreset,
  output wire     hreset_sync,
  
  input  wire     core_reset,
  
  input  wire     refclk,
  output wire     refclk_scan,
  output wire     refclk_reset,
  
  input  wire     fbclk,
  input  wire     enable_fbclk,
  input  wire     fbclk_reset_in,
  output wire     fbclk_scan,
  output wire     fbclk_reset,
  
  
  input  wire     vco0_clk,
  input  wire     vco0_clk_en,
  output wire     vco0_clk_scan,
  output wire     vco0_clk_reset,
  
  input  wire     vco1_clk,
  input  wire     vco1_clk_en,
  output wire     vco1_clk_scan,
  output wire     vco1_clk_reset,
  
  
  input  wire     vco2_clk,
  input  wire     vco2_clk_en,
  output wire     vco2_clk_scan,
  output wire     vco2_clk_reset
);

wav_clock_mux  u_wav_clock_mux_hclk_scan (
  .clk0    ( hclk             ),  
  .clk1    ( core_scan_clk    ),  
  .sel     ( core_scan_mode   ),  
  .clk_out ( hclk_scan        )); 

wav_reset_sync u_wav_reset_sync_hreset_hclk (
  .clk           ( hclk_scan               ),  
  .scan_ctrl     ( core_scan_asyncrst_ctrl ),  
  .reset_in      ( hreset                  ),  
  .reset_out     ( hreset_sync             )); 




wav_clock_mux  u_wav_clock_mux_refclk_scan (
  .clk0    ( refclk              ),  
  .clk1    ( core_scan_clk       ),  
  .sel     ( core_scan_mode      ),  
  .clk_out ( refclk_scan         )); 

wav_reset_sync u_wav_reset_sync_core_reset_refclk (
  .clk           ( refclk_scan                ),  
  .scan_ctrl     ( core_scan_asyncrst_ctrl    ),  
  .reset_in      ( core_reset                 ),  
  .reset_out     ( refclk_reset               )); 


//-----------------------------------
// FBCLK
//-----------------------------------
wire fbclk_scan_pre_gate;
wav_clock_mux  u_wav_clock_mux_fbclk_scan (
  .clk0    ( fbclk               ),  
  .clk1    ( core_scan_clk       ),  
  .sel     ( core_scan_mode      ),  
  .clk_out ( fbclk_scan_pre_gate )); 

wav_reset_sync u_wav_reset_sync_core_reset_fbclk (
  .clk           ( fbclk_scan_pre_gate          ),  
  .scan_ctrl     ( core_scan_asyncrst_ctrl      ),  
  .reset_in      ( core_reset || fbclk_reset_in ),  
  .reset_out     ( fbclk_reset                  )); 

wav_cen u_wav_cen_fbclk (
  .clk_in              ( fbclk_scan_pre_gate  ),  
  .reset               ( fbclk_reset          ),  
  .enable              ( enable_fbclk         ),      
  .test_en             ( core_scan_mode       ),  
  .disable_clkgate     ( 1'b0                 ),  
  .clk_out             ( fbclk_scan           )); 


//-----------------------------------
// VCO0
//-----------------------------------
wire vco0_clk_scan_pre_gate;
wire vco0_clk_scan_pre_div;
reg  vco0_div2;
wav_clock_mux  u_wav_clock_mux_vco0clk_scan (
  .clk0    ( vco0_clk               ),  
  .clk1    ( core_scan_clk          ),  
  .sel     ( core_scan_mode         ),  
  .clk_out ( vco0_clk_scan_pre_gate )); 

wav_reset_sync u_wav_reset_sync_core_reset_vco0clk (
  .clk           ( vco0_clk_scan_pre_gate     ),  
  .scan_ctrl     ( core_scan_asyncrst_ctrl    ),  
  .reset_in      ( core_reset                 ),  
  .reset_out     ( vco0_clk_reset             )); 

wav_cen u_wav_cen_vco0_clk (
  .clk_in              ( vco0_clk_scan_pre_gate   ),  
  .reset               ( vco0_clk_reset           ),  
  .enable              ( vco0_clk_en              ),      
  .test_en             ( core_scan_mode           ),  
  .disable_clkgate     ( 1'b0                     ),  
  .clk_out             ( vco0_clk_scan            )); 

//-----------------------------------
// VCO1
//-----------------------------------
wire vco1_clk_scan_pre_gate;
wav_clock_mux  u_wav_clock_mux_vco1clk_scan (
  .clk0    ( vco1_clk               ),  
  .clk1    ( core_scan_clk          ),  
  .sel     ( core_scan_mode         ),  
  .clk_out ( vco1_clk_scan_pre_gate )); 

wav_reset_sync u_wav_reset_sync_core_reset_vco1clk (
  .clk           ( vco1_clk_scan_pre_gate     ),  
  .scan_ctrl     ( core_scan_asyncrst_ctrl    ),  
  .reset_in      ( core_reset                 ),  
  .reset_out     ( vco1_clk_reset             )); 

wav_cen u_wav_cen_vco1_clk (
  .clk_in              ( vco1_clk_scan_pre_gate   ),  
  .reset               ( vco1_clk_reset           ),  
  .enable              ( vco1_clk_en              ),      
  .test_en             ( core_scan_mode           ),  
  .disable_clkgate     ( 1'b0                     ),  
  .clk_out             ( vco1_clk_scan            )); 


//-----------------------------------
// VCO2
//-----------------------------------
wire vco2_clk_scan_pre_gate;
wav_clock_mux  u_wav_clock_mux_vco2clk_scan (
  .clk0    ( vco2_clk               ),  
  .clk1    ( core_scan_clk          ),  
  .sel     ( core_scan_mode         ),  
  .clk_out ( vco2_clk_scan_pre_gate )); 

wav_reset_sync u_wav_reset_sync_core_reset_vco2clk (
  .clk           ( vco2_clk_scan_pre_gate     ),  
  .scan_ctrl     ( core_scan_asyncrst_ctrl    ),  
  .reset_in      ( core_reset                 ),  
  .reset_out     ( vco2_clk_reset             )); 
  
wav_cen u_wav_cen_vco2_clk (
  .clk_in              ( vco2_clk_scan_pre_gate   ),  
  .reset               ( vco2_clk_reset           ),  
  .enable              ( vco2_clk_en              ),      
  .test_en             ( core_scan_mode           ),  
  .disable_clkgate     ( 1'b0                     ),  
  .clk_out             ( vco2_clk_scan            )); 

endmodule
