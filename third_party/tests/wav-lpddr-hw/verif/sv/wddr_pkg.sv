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

package wddr_pkg;

  import uvm_pkg::*;
  import wav_APB_pkg::*;

`include "uvm_macros.svh"

`include "ddr_global_define.vh"
`include "ddr_cmn_csr_defs.vh"
`include "ddr_fsw_csr_defs.vh"
`include "ddr_cmn_wrapper_define.vh"
`include "wav_reg_model_mvp_pll.svh"
`include "ddr_ctrl_csr_defs.vh"
`include "ddr_ca_csr_defs.vh"
`include "ddr_dfi_csr_defs.vh"
`include "ddr_dfich_csr_defs.vh"
`include "ddr_dq_csr_defs.vh"
`include "wav_mcu_csr_defs.vh"
`include "wav_mcuintf_csr_defs.vh"
`include "wav_mcutop_csr_defs.vh"

//--REGISTER MODEL FOR ddr_phy TOP
`include "register/wddr_reg_model.svh"
`include "register/wddr_reg_model.sv"

//--ENV INCLUDES
`include "tb_top/wddr_tb.sv"

endpackage

//--SEQUENCES INCLUDES
//`include "sequences/wddr_seq_lib.svh"
