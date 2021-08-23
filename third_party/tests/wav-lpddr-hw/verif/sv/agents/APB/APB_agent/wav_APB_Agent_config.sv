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
`ifndef WAV_APB_AGENT_CONFIG_SV
`define WAV_APB_AGENT_CONFIG_SV
//------------------------------------------------------------------------------
//
// CLASS: wav_APB_Agent_config
//
//------------------------------------------------------------------------------

class wav_APB_Agent_config extends uvm_object;

  bit [31:0] slv_err_addr[*];
  bit [9:0] prdy_max_dly;
  bit [9:0] prdy_dly_fixed;
  bit       prdy_rand_dly_en;

  bit       wait_for_pready_low;
	// UVM object utils macro
	`uvm_object_utils_begin(wav_APB_Agent_config)
	`uvm_object_utils_end

  // ***************************************************************** new *****
   // new - constructor
   function new(string name = "wav_APB_Agent_config");
     super.new(name);
     this.wait_for_pready_low = 0;
   endfunction: new

  // ************************************************* update_slv_err_addr *****
  function void update_slv_err_addr(bit add_nDel, bit [31:0] addr_a);
    if(!slv_err_addr.exists(addr_a))begin
      if(add_nDel) slv_err_addr[addr_a] = 1;
      else `uvm_error("NO_ADDR_SLVERR", $psprintf("Address not found in array to del : %0h", addr_a))
    end
    else begin
      if(!add_nDel) slv_err_addr.delete(addr_a);
    end
  endfunction : update_slv_err_addr

  // ********************************************************* get_slv_err *****
  function bit get_slv_err(bit [31:0] addr_a);
  //function bit get_slv_err(bit psel);
    `uvm_info("GET_SLV_ERR", $psprintf("ENTERED_THE_GET_SLV_ERR_ADDR=%0h", addr_a),UVM_INFO)
    if(slv_err_addr.exists(addr_a)) begin
      get_slv_err = 1;
      `uvm_info("GET_SLV_ERR", $psprintf("GOT_THE_SLVERR=%0h", get_slv_err),UVM_INFO)
    end  
    else begin
     get_slv_err = 0;
    `uvm_info("GET_SLV_ERR", $psprintf("NOT_GOT_THE_SLVERR=%0h", get_slv_err),UVM_INFO)
    end
  endfunction : get_slv_err

endclass : wav_APB_Agent_config

`endif

