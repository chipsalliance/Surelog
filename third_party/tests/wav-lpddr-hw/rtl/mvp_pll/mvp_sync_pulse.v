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

module mvp_sync_pulse(
  input  wire     clk_in,
  input  wire     clk_in_reset,
  input  wire     data_in,
  
  input  wire     clk_out,
  input  wire     clk_out_reset,
  output wire     data_out  
);

reg     clk_in_pulse;

always @(posedge clk_in or posedge clk_in_reset) begin
  if(clk_in_reset) begin
    clk_in_pulse    <= 1'b0;
  end else begin
    clk_in_pulse    <= data_in ? ~clk_in_pulse : clk_in_pulse;
  end
end


wire pulse_demeted;
reg  pulse_demeted_ff3;
demet_reset u_demet_reset (
  .clk     ( clk_out        ),  
  .reset   ( clk_out_reset  ),  
  .sig_in  ( clk_in_pulse   ),  
  .sig_out ( pulse_demeted  )); 

always @(posedge clk_out or posedge clk_out_reset) begin
  if(clk_out_reset) begin
    pulse_demeted_ff3    <= 1'b0;
  end else begin
    pulse_demeted_ff3    <= pulse_demeted;
  end
end

assign data_out = pulse_demeted ^ pulse_demeted_ff3;


endmodule
