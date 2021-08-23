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
import "DPI-C" function string getenv(input string env_name);

class wddr_mcu_load_mem extends wddr_base_seq;

  `uvm_object_utils(wddr_mcu_load_mem);

  function new(string name="wddr_mcu_load_mem");
    super.new(name);
  endfunction

  virtual task body();
    begin
      uvm_mem ibex_itcm;
      uvm_mem ibex_dtcm;
      uvm_status_e  status;
      bit [31:0] value;
      bit [31:0] memory[$];
      reg        file_result;

      string      wtm_env = "";
      string      wtm_test= "";
      string      itcm_file;
      integer     itcm_filehandle;
      string      dtcm_file;
      integer     dtcm_filehandle;
      bit [7:0]   b0, b1, b2, b3;

     // wtm_env =  getenv("WTM");

     // if(wtm_env == "") begin
     //   `uvm_fatal("WTM ENV Variable not set!", "Couldn't not find WTM ENV VAR");
     // end

     // wtm_test =  getenv("WTM_SW_TEST");
     // if(wtm_test == "") begin
     //   `uvm_fatal("WTM_SW_TEST Variable not set!", "Couldn't not find WTM_SW_TEST ENV VAR");
     // end

     // $display("%s", wtm_env);

      itcm_file = {"/prj/wavious/dev/frontend/core/workareas/rraman/wddr100/sw/tests/zqcal/ramfiles_ahb/itcm_65536x4_tcm0_b0_byte03_byte00.ram"};
      dtcm_file = {"/prj/wavious/dev/frontend/core/workareas/rraman/wddr100/sw/tests/zqcal/ramfiles_ahb/dtcm_65536x4_tcm0_b0_byte03_byte00.ram"};

      ibex_itcm = reg_model.get_mem_by_name("WDDR_MCU_IBEX_ITCM");
      ibex_dtcm = reg_model.get_mem_by_name("WDDR_MCU_IBEX_DTCM");

      itcm_filehandle = $fopen(itcm_file, "r");
      `uvm_info(get_type_name(),$psprintf("Loading ITCM from %s", itcm_file), UVM_MEDIUM)
      while(!$feof(itcm_filehandle)) begin
        file_result = $fscanf(itcm_filehandle, "%8h", value);
        memory.push_back(value);
      end

      //file_result = $fcloser(itcm_file);

      foreach(memory[i]) begin
        ibex_itcm.write(status, i, memory[i]);
      end
      memory.delete();

      dtcm_filehandle = $fopen(dtcm_file, "r");
      `uvm_info(get_type_name(),$psprintf("Loading DTCM from %s", dtcm_file), UVM_MEDIUM)
      while(!$feof(dtcm_filehandle)) begin
        file_result = $fscanf(dtcm_filehandle, "%8h", value);
        memory.push_back(value);
      end

      foreach(memory[i]) begin
        ibex_dtcm.write(status, i, memory[i]);
      end

      set_mcu_en ( .fetch_en(1'b1), .debug_en(1'b0));
      check_mcu_exec_status ;
      por();
      #2000us;
      set_mcu_en ( .fetch_en(1'b1), .debug_en(1'b0));
      #100us;
      por();
      set_mcu_en ( .fetch_en(1'b1), .debug_en(1'b0));
      #2000us;
      check_mcu_exec_status ;

    end

  endtask

endclass
