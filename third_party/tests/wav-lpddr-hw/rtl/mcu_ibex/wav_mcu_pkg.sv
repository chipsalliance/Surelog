
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

`ifndef WAV_MCU_PKG
`define WAV_MCU_PKG

`timescale 1ps/1ps

package wav_mcu_pkg;

   // ------------------------------------------------------------------------
   // Memory Map
   // ------------------------------------------------------------------------

   parameter WAV_MCUTOP_OFFSET      = 32'h00000000;
   parameter WAV_MCUINTF_OFFSET     = 32'h00004000;
   parameter WAV_MCUCSR_OFFSET      = 32'h00008000;
   parameter WAV_MCU_ITCM_OFFSET    = 32'h00010000;
   parameter WAV_MCU_DTCM_OFFSET    = 32'h00050000;

   parameter WAV_MCUTOP_SIZE        = 32'd 16384;
   parameter WAV_MCUINTF_SIZE       = 32'd 16384;
   parameter WAV_MCUCSR_SIZE        = 32'd 32768;
   parameter WAV_MCU_ITCM_SIZE      = 32'd 65536;
   parameter WAV_MCU_DTCM_SIZE      = 32'd 65536;

   // ------------------------------------------------------------------------
   // Memory Map
   // ------------------------------------------------------------------------

   parameter WAV_NUM_IRQ            = 5'd24 ;

endpackage : wav_mcu_pkg
`endif // WAV_MCU_PKG
