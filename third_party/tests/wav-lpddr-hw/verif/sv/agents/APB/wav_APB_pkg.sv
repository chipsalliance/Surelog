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
`include "APB/APB_agent/wav_APB_if.sv"

package wav_APB_pkg;
   import uvm_pkg::*;

  `include "uvm_macros.svh"
  `include "APB/APB_agent/wav_defines.svh"
  `include "APB/wav_APB_lib.svh"

endpackage
