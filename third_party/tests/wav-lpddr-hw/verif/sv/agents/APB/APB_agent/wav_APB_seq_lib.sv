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

import uvm_pkg::*;

// The base wav APB base sequence. All children sequences inherit this behavior.
// It raises/drops objections in the pre/post_body.

virtual class wav_APB_base_seq extends uvm_sequence #(wav_APB_transfer);

  function new(string name="wav_APB_base_seq");
    super.new(name);
  endfunction

  // Raise objection in pre_body.
  virtual task pre_body();
    if (starting_phase!=null) begin
      `uvm_info(get_type_name(),
		  $psprintf("%s pre_body() raising %s objection", get_sequence_path(), starting_phase.get_name()), UVM_MEDIUM);
      starting_phase.raise_objection(this);

	  //if(regmodel==null)

    end
  endtask

  // Drop objection in post_body.
  virtual task post_body();
    if (starting_phase!=null) begin
      `uvm_info(get_type_name(), $psprintf("%s post_body() dropping %s objection", get_sequence_path(), starting_phase.get_name()), UVM_MEDIUM);
      starting_phase.drop_objection(this);
    end
  endtask

endclass

// TODO Define sequences in the wav APB sequence library
// For example:
class wav_APB_example_seq extends wav_APB_base_seq;

  function new(string name="wav_APB_example_seq");
    super.new(name);
  endfunction

  `uvm_object_utils(wav_APB_example_seq)

  rand int unsigned nof_transfers = 1;
  constraint nof_transfers_ct { (nof_transfers <= 10); }
  wav_APB_transfer seq1;

  virtual task body();
    //for (int i=0; i< 8; i++) begin
       //`uvm_do(req);
      //  seq1 = new("seq1");

	    //`uvm_do_with(seq1, {seq1.data == i;seq1.addr == i;seq1.direction == 1;});
        `uvm_do_with(seq1, {seq1.data == 'hAAAAAAAA;seq1.addr == 'h00;seq1.direction == APB_WRITE;});
       //get_response(rsp);
    //end
  endtask

endclass

class apb_reg_base_seq extends uvm_sequence;

   uvm_status_e  status;
   uvm_reg       write_reg;
   uvm_reg       read_reg;

	// new - constructor
	function new(string name="apb_reg_base_seq");
		super.new(name);
	endfunction

    `uvm_object_utils(wav_APB_example_seq)

    //
    virtual function void get_model();
    	uvm_object temp_object;
	    uvm_reg_block temp_reg_block;

//	    if(reg_model == null )
//		  if(uvm_config_object::get(get_sequencer(),"","reg_model", temp_object)) begin
//			 if(!($cast(reg_model,temp_object)))
//				`uvm_fatal("BAD_CONFIG", "Sequence reg model is inocrrect")
//		  end
//		  else if (uvm_config_db #(uvm_reg_block)::get(get_sequencer(),"","reg_model", temp_reg_block))
//			     if(!($cast(reg_model, temp_reg_block)))
//			      `uvm_fatal("ERROR_ID", "class_name not found in the UVM factory!")

	    //else
		 // `uvm_fatal("NO_REG_CONFIG", "Reg Model is not set, Exiting")

    endfunction : get_model

   virtual task pre_start();
	   get_model();
   endtask

   virtual task pre_body();
     if (starting_phase!=null) begin
      `uvm_info(get_type_name(), $psprintf("%s pre_body() raising %s objection", get_sequence_path(), starting_phase.get_name()), UVM_MEDIUM);
      starting_phase.raise_objection(this);

    end
   endtask

  // Drop objection in post_body.
  virtual task post_body();
    if (starting_phase!=null) begin
      `uvm_info(get_type_name(), $psprintf("%s post_body() dropping %s objection", get_sequence_path(), starting_phase.get_name()), UVM_MEDIUM);
      starting_phase.drop_objection(this);
    end
  endtask

endclass : apb_reg_base_seq

class basic_reg_read_write extends apb_reg_base_seq;

	// new - constructor
	function new(string name="basic_reg_read_write_seq");
		super.new(name);
	endfunction

    `uvm_object_utils(basic_reg_read_write)

	virtual task body();

	  uvm_reg regs[$];
	  bit [63:0] rval;

	  `uvm_info(get_type_name(), $psprintf("%s Executing ", get_sequence_path()), UVM_MEDIUM);

  //    `reg_read("MASOC_D2D_RPLL_CTRL1",  rval)
  //    `reg_write("MASOC_D2D_RPLL_CTRL1", 'hff)
//	  `reg_read("MASOC_D2D_RPLL_CTRL1",  rval)

      //`reg_read("MASOC_D2D_RPLL_CTRL2",  rval)
      //`reg_write("MASOC_D2D_RPLL_CTRL2", 'hff)
	  //`reg_read("MASOC_D2D_RPLL_CTRL2",  rval)

	  #1us;
	  `uvm_info(get_type_name(), $psprintf("%s Sequence completed ", get_sequence_path()), UVM_MEDIUM);

	endtask : body

endclass
