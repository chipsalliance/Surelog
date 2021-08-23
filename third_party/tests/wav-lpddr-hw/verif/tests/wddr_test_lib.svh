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
`include "tests/wddr_base_test.sv"
`include "tests/regs/wddr_reg_reset_test.sv"
`include "tests/regs/wddr_reg_bitbash_test.sv"
`include "tests/regs/wddr_reg_access_test.sv"
`include "tests/regs/wddr_reg_direct_test.sv"
`include "tests/dt/wddr_dt_pll_test.sv"
`include "tests/dt/wddr_dt_mcu_test.sv"
`include "tests/dt/wddr_dt_mcuboot_test.sv"
`include "tests/dt/wddr_dt_mcuhost_test.sv"
`include "tests/dt/wddr_dt_ddr_test.sv"
`include "tests/dt/wddr_dt_ddr_spice_test.sv"
`include "tests/dt/wddr_dt_dfistatus_test.sv"
`include "tests/dt/wddr_dt_freqsw_test.sv"
`ifdef DFIMC
//`include "tests/wddr_dfi_TEST_PAD_test.sv"
//`include "tests/wddr_dfi_Error_response_test.sv"
`include "tests/wddr_dfi_test.sv"
`include "tests/wddr_dfifreeze_test.sv"
`include "tests/wddr_dfihiz_test.sv"
//`include "tests/FC_Sweep/wddr_dfi_sweep_m0_rx_test.sv"  //new test for sweep_m0_test
`include "tests/FC_Sweep/wddr_dfi_sweep_m0_test.sv"  //new test for sweep_m0_test
`include "tests/PI_Sweep/wddr_dfi_PI_0_m0_test.sv"  //new test for sweep_m0_test
`include "tests/PI_Sweep/wddr_dfi_PI_0_m1_test.sv"  //new test for sweep_m0_test
`include "tests/PI_Sweep/wddr_dfi_PI_RT_m0_test.sv"  //new test for sweep_m0_test
`include "tests/PI_Sweep/wddr_dfi_PI_RT_m1_test.sv"  //new test for sweep_m0_test
`include "tests/PI_Sweep/wddr_dfi_rxrdqs_m0_test.sv"  //new test for sweep_m0_test
`include "tests/PI_Sweep/wddr_dfi_rxrdqs_m1_test.sv"  //new test for sweep_m0_test
`include "tests/PI_Sweep/wddr_dfi_rx_ren_pi_m0_test.sv"  //new test for sweep_m0_test
`include "tests/PI_Sweep/wddr_dfi_rx_ren_pi_m1_test.sv"  //new test for sweep_m0_test
`include "tests/PI_Sweep/wddr_dfi_rx_rcs_pi_m0_test.sv"  //new test for sweep_m0_test
`include "tests/PI_Sweep/wddr_dfi_rx_rcs_pi_m1_test.sv"
`include "tests/PI_Sweep/wddr_dfi_rxrdqs_m0_test.sv"  //new test for sweep_m0_test
`include "tests/PI_Sweep/wddr_dfi_rxrdqs_m1_test.sv"  //new test for sweep_m0_test
`include "tests/PI_Sweep/wddr_dfi_rx_ren_pi_m0_test.sv"  //new test for sweep_m0_test
`include "tests/PI_Sweep/wddr_dfi_rx_ren_pi_m1_test.sv"  //new test for sweep_m0_test
`include "tests/PI_Sweep/wddr_dfi_rx_rcs_pi_m0_test.sv"  //new test for sweep_m0_test
`include "tests/PI_Sweep/wddr_dfi_rx_rcs_pi_m1_test.sv"  //new test for sweep_m0_test
//`include "tests/PI_Sweep/wddr_dfi_PI_RT_m0_test.sv"  //new test for sweep_m0_test
`include "tests/FC_Sweep/wddr_dfi_sweep_m1_test.sv"  //new test for sweep_m1_test
`include "tests/FC_Sweep/wddr_dfi_sweep_m0_12_test.sv"  //new test for sweep_m1_test
`include "tests/FC_Sweep/wddr_dfi_sweep_m1_12_test.sv"  //new test for sweep_m1_test
`include "tests/FC_Sweep/wddr_dfi_sweep_m0_14_test.sv"  //new test for sweep_m1_test
`include "tests/FC_Sweep/wddr_dfi_sweep_m1_14_test.sv"  //new test for sweep_m1_test
`include "tests/FC_Sweep/wddr_dfi_sweep_m0_dqs_test.sv"  //new test for sweep_m1_test
`include "tests/FC_Sweep/wddr_dfi_sweep_m1_dqs_test.sv"  //new test for sweep_m1_test
`include "tests/FC_Sweep/wddr_dfi_sweep_m0_12_dqs_test.sv"  //new test for sweep_m1_test
`include "tests/FC_Sweep/wddr_dfi_sweep_m1_12_dqs_test.sv"  //new test for sweep_m1_test
`include "tests/FC_Sweep/wddr_dfi_sweep_m1_14_dqs_test.sv"  //new test for sweep_m1_test
`include "tests/FC_Sweep/wddr_dfi_sweep_m0_14_dqs_test.sv"  //new test for sweep_m1_test
`include "tests/wddr_dfi_low_power_test.sv"
`include "tests/wddr_dfi_update_test.sv"
`include "tests/wddr_dfi_phymaster_test.sv"
`include "tests/wddr_dfi_2nmode_test.sv"
`include "tests/wddr_dfi_status_test.sv"
`include "tests/wddr_dfi_r0_allcmd_test.sv"
`include "tests/wddr_dfi_r1_allcmd_test.sv"
`include "tests/wddr_dfi_rank_switch_test.sv"
`include "tests/wddr_dfi_r0_walkgap_allcmd_test.sv"
`include "tests/wddr_dfi_r0_tccd1_test.sv"
`include "tests/wddr_dfi_r1_tccd1_test.sv"
`include "tests/wddr_dfi_walkgap_rankswitch_test.sv"
`include "tests/wddr_dfi_r1_walkgap_allcmd_test.sv"
`include "tests/wddr_dfi_refreshall_test.sv"
`include "tests/wddr_dfi_DRVR_ConTXM0_test.sv"  //DRVR
`include "tests/wddr_dfi_DRVR_DQ_ConTXM0_test.sv"  //DRVR
`include "tests/wddr_dfi_LPDE_TX_m0_test.sv" //LPDE TX
`include "tests/wddr_dfi_LPDE_RX_m0_test.sv" //LPDE RX
`include "tests/wddr_dfi_LPDE_RX_SA_m0_test.sv" //LPDE RX SA
`include "tests/wddr_dfi_LPDE_TX_m0_r1_test.sv" //LPDE TX M0_R1/
`include "tests/wddr_dfi_LPDE_RX_m0_r1_test.sv" //LPDE RX M0_R1
`include "tests/wddr_dfi_LPDE_RX_SA_m0_r1_test.sv" //LPDE RXSA M0_R1
`include "tests/wddr_dfi_LPDE_TX_m1_r0_test.sv" //LPDE TX M1_R0
`include "tests/wddr_dfi_LPDE_RX_m1_r0_test.sv" //LPDE RX M1_R0
`include "tests/wddr_dfi_LPDE_RX_SA_m1_r0_test.sv" //LPDE RXSA M1_R0
//`include "tests/wddr_dfi_LPDE_TX_m1_r1_test.sv" //LPDE TX M1_R1
`include "tests/wddr_dfi_LPDE_RX_m1_r1_test.sv" //LPDE RX M1_R1
`include "tests/wddr_dfi_LPDE_RX_SA_m1_r1_test.sv" //LPDE RXSA M1_R1
`include "tests/wddr_dfi_refreshbank_test.sv"
`include "tests/wddr_dfi_wrap32_rdap32_test.sv"
//`include "tests/wddr_dfi_DEBUG_BUS_test.sv"

//`include "tests/wddr_dfi_wr16_pre_test.sv"
//`include "tests/wddr_dfi_wr32_pre_test.sv"
`include "tests/wddr_dfi_rand_test.sv"
`include "tests/wddr_dfi_freqsw_test.sv"
`include "tests/wddr_dfi_turn_test.sv"

`include "tests/mcu/wddr_mcu_freqsw_test.sv"
`include "tests/mcu/wddr_mcu_dfiupdate_test.sv"
`include "tests/mcu/wddr_mcu_dfiphymas_test.sv"
`include "tests/mcu/wddr_mcu_dfilp_test.sv"
`include "tests/mcu/wddr_mcu_load_mem_test.sv"
`endif
