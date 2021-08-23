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
//`ifdef RAMFILE_DIR_<testcase name>
//   `define RAMFILEPATH "$sw/tests/<test case dir>/ramfiles/"
//`endif

`ifdef RAMFILE_DIR_SAMPLE
   `define RAMFILEPATH "$sw/tests/sample/ramfiles/"
`endif

`ifdef RAMFILE_DIR_DEBUGGER
   `define RAMFILEPATH "$sw/tests/debugger/ramfiles/"
`endif

`ifdef RAMFILE_DIR_PLL_BOOT_VCO0
   `define RAMFILEPATH "$sw/tests/pll_boot_vco0/ramfiles/"
`endif

`ifdef RAMFILE_DIR_CONTROLLER_BOOT
   `define RAMFILEPATH "$sw/tests/controller_boot/ramfiles/"
`endif

`ifdef RAMFILE_DIR_CONTROLLER_PLL_BOOT_CAL
   `define RAMFILEPATH "$sw/tests/controller_pll_boot_cal/ramfiles/"
`endif

`ifdef RAMFILE_DIR_TRAIN_BUFFER
   `define RAMFILEPATH "$sw/tests/train_buffer/ramfiles/"
`endif

`ifdef RAMFILE_DIR_SANDBOX
   `define RAMFILEPATH "$sw/tests/sandbox/ramfiles/"
`endif

`ifdef RAMFILE_DIR_DFI_BUFFER
   `define RAMFILEPATH "$sw/tests/dfi_buffer/ramfiles/"
`endif

`ifdef RAMFILE_DIR_PMON
   `define RAMFILEPATH "$sw/tests/pmon/ramfiles/"
`endif

`ifdef RAMFILE_DIR_ZQCAL
   `define RAMFILEPATH "$sw/tests/zqcal/ramfiles/"
`endif

`ifdef RAMFILE_DIR_SACAL
   `define RAMFILEPATH "$sw/tests/sacal/ramfiles/"
`endif

`ifdef RAMFILE_DIR_AHB
   `define RAMFILEPATH "$sw/tests/ahb/ramfiles/"
`endif

`ifdef RAMFILE_DIR_HOST_API
   `define RAMFILEPATH "$sw/tests/main_wddr/ramfiles/"
`endif

`ifdef RAMFILE_DIR_MESSENGER
   `define RAMFILEPATH "$sw/tests/messenger/ramfiles/"
`endif

`ifdef RAMFILE_DIR_WDDR_BOOT
   `define RAMFILEPATH "$sw/tests/wddr_boot/ramfiles/"
`endif

`ifdef RAMFILE_DIR_DV_LOG
   `define RAMFILEPATH "$sw/tests/dv_log/ramfiles/"
`endif

`ifdef RAMFILE_DIR_CBT
   `define RAMFILEPATH "$sw/tests/cbt/ramfiles/"
`endif

`ifdef RAMFILE_DIR_WR_LVL
   `define RAMFILEPATH "$sw/tests/wr_lvl/ramfiles/"
`endif

`ifdef RAMFILE_DIR_REN
   `define RAMFILEPATH "$sw/tests/ren/ramfiles/"
`endif

`ifdef RAMFILE_DIR_RD_EYE
   `define RAMFILEPATH "$sw/tests/rd_eye/ramfiles/"
`endif

`ifdef RAMFILE_DIR_WR_EYE
   `define RAMFILEPATH "$sw/tests/wr_eye/ramfiles/"
`endif

`ifdef RAMFILE_DIR_RETIMER
   `define RAMFILEPATH "$sw/tests/retimer/ramfiles/"
`endif

`ifdef RAMFILE_DIR_FREQ_TRAIN
   `define RAMFILEPATH "$sw/tests/freq_train/ramfiles/"
`endif

`ifdef RAMFILE_DIR_DRIVER_TEST
   `define RAMFILEPATH "$sw/tests/driver_test/ramfiles/"
`endif

`define MCU_ITCM_HIER `TB_HIER.u_mcu.u_itcm
`define MCU_DTCM_HIER `TB_HIER.u_mcu.u_dtcm

`ifdef WAV_RAM_TSMC12LPP
`ifdef RAMFILEPATH
// MCU ITCM
defparam  `MCU_ITCM_HIER.tcm_sram[0].tcm_32bit.tcm_sram.cdeFileInit =  {`RAMFILEPATH, "itcm_2048x4_tcm0_b0_byte03_byte00.ram"} ;
defparam  `MCU_ITCM_HIER.tcm_sram[1].tcm_32bit.tcm_sram.cdeFileInit =  {`RAMFILEPATH, "itcm_2048x4_tcm0_b1_byte03_byte00.ram"} ;
defparam  `MCU_ITCM_HIER.tcm_sram[2].tcm_32bit.tcm_sram.cdeFileInit =  {`RAMFILEPATH, "itcm_2048x4_tcm0_b2_byte03_byte00.ram"} ;
defparam  `MCU_ITCM_HIER.tcm_sram[3].tcm_32bit.tcm_sram.cdeFileInit =  {`RAMFILEPATH, "itcm_2048x4_tcm0_b3_byte03_byte00.ram"} ;

// MCU DTCM
defparam  `MCU_DTCM_HIER.tcm_sram[0].tcm_32bit.tcm_sram.cdeFileInit =  {`RAMFILEPATH, "dtcm_2048x4_tcm0_b0_byte03_byte00.ram"} ;
defparam  `MCU_DTCM_HIER.tcm_sram[1].tcm_32bit.tcm_sram.cdeFileInit =  {`RAMFILEPATH, "dtcm_2048x4_tcm0_b1_byte03_byte00.ram"} ;
defparam  `MCU_DTCM_HIER.tcm_sram[2].tcm_32bit.tcm_sram.cdeFileInit =  {`RAMFILEPATH, "dtcm_2048x4_tcm0_b2_byte03_byte00.ram"} ;
defparam  `MCU_DTCM_HIER.tcm_sram[3].tcm_32bit.tcm_sram.cdeFileInit =  {`RAMFILEPATH, "dtcm_2048x4_tcm0_b3_byte03_byte00.ram"} ;
`endif
`endif
