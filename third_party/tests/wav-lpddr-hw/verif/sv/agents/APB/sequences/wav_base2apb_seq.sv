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
class wav_base2apb_seq extends uvm_sequence#(wav_APB_transfer);

    wav_base_transaction wav_xtrans;
	wav_APB_sequencer    apb_sequencer;

    bit [7:0]               data[];

    `uvm_object_utils( wav_base2apb_seq)

    function new(string name = "wav_base2apb_seq");
	  super.new(name);  
    endfunction

    virtual task body();
       
      `uvm_info(get_type_name(), $psprintf("1.PRE-CREATE OF TRANSACTION"), UVM_LOW);

      `uvm_create(req);

      `uvm_info(get_type_name(), $psprintf("2.POST-CREATE, PRE-RUN OF TRANSACTION"), UVM_LOW);

       req.addr = wav_xtrans.addr;

       if(wav_xtrans.rw == WAV_WRITE) begin
         req.direction = APB_WRITE;

        foreach (wav_xtrans.data[i])
         req.data[(i*8)+:8] = wav_xtrans.data[i];
       end
       else begin
        req.direction = APB_READ;   
  	   end    

	  `uvm_send(req);

      `uvm_info(get_type_name(), $psprintf("3.POST-CREATE, PPOST-RUN, PRE-RSP OF TRANSACTION"), UVM_LOW);

      if(wav_xtrans.rw == WAV_READ) begin

       get_response(rsp);   

       wav_xtrans.addr  = rsp.addr;
       wav_xtrans.data.delete();  
                   
       wav_xtrans.data.push_back(rsp.data[7:0]);
       wav_xtrans.data.push_back(rsp.data[15:8]);
       wav_xtrans.data.push_back(rsp.data[23:16]);
       wav_xtrans.data.push_back(rsp.data[31:24]);
		             
	   `uvm_info(get_type_name(), "--------PRINTING THE RSP ITEM--------", UVM_DEBUG);  
  
       wav_xtrans.print();   
      end
      
    `uvm_info(get_type_name(), "done sequence", UVM_LOW);
    endtask

endclass
