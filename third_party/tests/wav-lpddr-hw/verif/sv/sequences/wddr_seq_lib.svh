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
import wddr_pkg::*;
import ddr_global_pkg::*;

`include "sv/sequences/wddr_config.sv"
`include "sv/sequences/wddr_base_seq.sv"
`include "sv/sequences/wddr_bringup_seq.sv"
`include "sv/sequences/wddr_mcu_load_mem.sv"
`include "sv/sequences/regs/wddr_reg_reset_seq.sv"
`include "sv/sequences/regs/wddr_reg_bitbash_seq.sv"
`include "sv/sequences/regs/wddr_reg_access_seq.sv"
`include "sv/sequences/regs/wddr_reg_direct_seq.sv"
`include "sv/sequences/dt/wddr_dt_pll_seq.sv"
`include "sv/sequences/dt/wddr_dt_ddr_seq.sv"
`include "sv/sequences/dt/wddr_dt_ddr_spice_seq.sv"
`include "sv/sequences/dt/wddr_dt_dfistatus_seq.sv"
`include "sv/sequences/dt/wddr_dt_mcu_seq.sv"
`include "sv/sequences/dt/wddr_dt_freqsw_seq.sv"
//`include "sv/sequences/dfimc/dfiSeqlib.sv"
