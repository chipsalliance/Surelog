// Copyright (C) 2019-2021  The SymbiFlow Authors.
//
// Use of this source code is governed by a ISC-style
// license that can be found in the LICENSE file or at
// https://opensource.org/licenses/ISC
//
// SPDX-License-Identifier: ISC


/*
:name: uvm_sequence
:description: uvm_sequence test
:tags: uvm uvm-classes
:type: simulation parsing
*/

import uvm_pkg::*;
`include "uvm_macros.svh"

class C extends uvm_sequence;
    function new(string name);
        super.new(name);
    endfunction

    virtual task pre_body();
        `uvm_info (get_type_name(), "pre_body()", UVM_LOW)
    endtask
   
    virtual task pre_do(bit is_item);
        `uvm_info (get_type_name(), "pre_do()", UVM_LOW)
    endtask
   
    virtual function void mid_do(uvm_sequence_item this_item);
        `uvm_info (get_type_name(), "mid_do()", UVM_LOW)
    endfunction
   
    virtual task body();
        `uvm_info (get_type_name(), "body()", UVM_LOW)
    endtask
   
    virtual function void post_do(uvm_sequence_item this_item);
        `uvm_info (get_type_name(), "post_do()", UVM_LOW)
    endfunction
   
    virtual task post_body();
        `uvm_info (get_type_name(), "post_body()", UVM_LOW)
    endtask
endclass

module top;
	C obj;
	initial begin
		obj = new("C");
	end
endmodule
