

//----------------------------------------------------------------------
//  Copyright (c) 2011-2012 by Doulos Ltd.
//
//  Licensed under the Apache License, Version 2.0 (the "License");
//  you may not use this file except in compliance with the License.
//  You may obtain a copy of the License at
//
//  http://www.apache.org/licenses/LICENSE-2.0
//
//  Unless required by applicable law or agreed to in writing, software
//  distributed under the License is distributed on an "AS IS" BASIS,
//  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//  See the License for the specific language governing permissions and
//  limitations under the License.
//----------------------------------------------------------------------

// First Steps with UVM - Nested Sequences

// Author: John Aynsley, Doulos
// Date:   13-Sep-2012


`include "uvm_macros.svh"

package my_pkg;

  import uvm_pkg::*;

  class my_transaction extends uvm_sequence_item;
  
    `uvm_object_utils(my_transaction)
  
    rand bit cmd;
    rand int addr;
    rand int data;
  
    constraint c_addr { addr >= 0; addr < 256; }
    constraint c_data { data >= 0; data < 256; }
    
    function new (string name = "");
      super.new(name);
    endfunction
    
    function string convert2string;
      return $sformatf("cmd=%b, addr=%0d, data=%0d", cmd, addr, data);
    endfunction

    function void do_copy(uvm_object rhs);
      my_transaction tx;
      $cast(tx, rhs);
      cmd  = tx.cmd;
      addr = tx.addr;
      data = tx.data;
    endfunction
    
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
      my_transaction tx;
      bit status = 1;
      $cast(tx, rhs);
      status &= (cmd  == tx.cmd);
      status &= (addr == tx.addr);
      status &= (data == tx.data);
      return status;
    endfunction

  endclass: my_transaction
  
  
  class my_config extends uvm_object;

    rand int count;
    rand int max_addr;
    
    constraint c_count    { count > 0; count < 128; }
    constraint c_max_addr { max_addr > 128; max_addr < 252; }

  endclass: my_config


  typedef uvm_sequencer #(my_transaction) my_sequencer;


  class child_sequence extends uvm_sequence #(my_transaction);
  
    `uvm_object_utils(child_sequence)
    
    rand int start_addr;
    
    constraint c_addr { start_addr >= 0; start_addr < 252; }
    
    function new (string name = "");
      super.new(name);
    endfunction

    task body;
      if (starting_phase != null)
        starting_phase.raise_objection(this);
        
      for (int i = 0; i < 4; i++)
      begin
        req = my_transaction::type_id::create("req");
        start_item(req);
        if( !req.randomize() with { addr == start_addr + i; } )
          `uvm_error("", "Randomize failed")
        finish_item(req);
      end
      
      if (starting_phase != null)
        starting_phase.drop_objection(this);
    endtask: body
   
  endclass: child_sequence
  
  
  class alt_child_sequence extends child_sequence;
  
    `uvm_object_utils(alt_child_sequence)

    rand bit [2:0] fixed_data;
    
    function new (string name = "");
      super.new(name);
    endfunction
    
    function void mid_do(uvm_sequence_item this_item);
      my_transaction tx;
      $cast(tx, this_item);
      tx.data = fixed_data;
    endfunction
    
  endclass: alt_child_sequence
  
    
  class top_sequence extends uvm_sequence #(my_transaction);

    `uvm_object_utils(top_sequence)
    `uvm_declare_p_sequencer(my_sequencer)
    
    function new (string name = "");
      super.new(name);
    endfunction

    task body;
      my_config cfg;
      int count, max_addr;

      if ( uvm_config_db #(my_config)::get(p_sequencer, "", "config", cfg) )
      begin
        count    = cfg.count;
        max_addr = cfg.max_addr;
      end
      else
      begin
        count    = 1;
        max_addr = 256;
      end
      
      if (starting_phase != null)
        starting_phase.raise_objection(this);

      repeat(count)
      begin
        child_sequence seq;
        seq = child_sequence::type_id::create("seq");
        if( !seq.randomize() with { start_addr < max_addr; } )
          `uvm_error("", "Randomize failed")
        seq.start(p_sequencer, this);
      end
      
      if (starting_phase != null)
        starting_phase.drop_objection(this);
    endtask: body
   
  endclass: top_sequence
  

  class my_driver extends uvm_driver #(my_transaction);
  
    `uvm_component_utils(my_driver)

    virtual dut_if dut_vi;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
      // Get interface reference from config database
      if( !uvm_config_db #(virtual dut_if)::get(this, "", "dut_if", dut_vi) )
        `uvm_error("", "uvm_config_db::get failed")
    endfunction 

    task run_phase(uvm_phase phase);
      forever
      begin
        seq_item_port.get_next_item(req);

        // Wiggle pins of DUT
        dut_vi.cmd  = req.cmd;
        dut_vi.addr = req.addr;
        dut_vi.data = req.data;
        @(posedge dut_vi.clock);

        seq_item_port.item_done();
      end
    endtask

  endclass: my_driver
  
  
  class my_env extends uvm_env;

    `uvm_component_utils(my_env)
    
    my_sequencer m_seqr;
    my_driver    m_driv;
    
    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction
 
    function void build_phase(uvm_phase phase);
      m_seqr = my_sequencer::type_id::create("m_seqr", this);
      m_driv = my_driver   ::type_id::create("m_driv", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
      m_driv.seq_item_port.connect( m_seqr.seq_item_export );
    endfunction
    
  endclass: my_env
  
  
  class my_test extends uvm_test;
  
    `uvm_component_utils(my_test)
    
    my_env m_env;
    
    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
      m_env = my_env::type_id::create("m_env", this);
    endfunction
    
    task run_phase(uvm_phase phase);
      my_config     cfg;
      top_sequence  seq;
      uvm_component component;
      my_sequencer  sequencer;
      
      cfg = new;
      if ( !cfg.randomize() with { count == 3; } )
        `uvm_error("", "Randomize failed")
      uvm_config_db #(my_config)::set(this, "*.m_seqr", "config", cfg);
      
      seq = top_sequence::type_id::create("seq");
      if( !seq.randomize() ) 
        `uvm_error("", "Randomize failed")
      seq.starting_phase = phase;

      component = uvm_top.find("*.m_seqr");
      if ($cast(sequencer, component))
        seq.start(sequencer);
    endtask
     
  endclass: my_test
  
  
  class my_test2 extends my_test;

    `uvm_component_utils(my_test2)

    function new (string name, uvm_component parent);
      super.new(name, parent);
    endfunction : new

    function void start_of_simulation_phase(uvm_phase phase);
      super.start_of_simulation_phase(phase);

      child_sequence::type_id::set_type_override( alt_child_sequence::get_type() );
    endfunction : start_of_simulation_phase

  endclass: my_test2
  

endpackage: my_pkg


module top;

  import uvm_pkg::*;
  import my_pkg::*;
  
  dut_if dut_if1 ();
  
  dut    dut1 ( .dif(dut_if1) );

  // Clock generator
  initial
  begin
    dut_if1.clock = 0;
    forever #5 dut_if1.clock = ~dut_if1.clock;
  end

  initial
  begin
    uvm_config_db #(virtual dut_if)::set(null, "*", "dut_if", dut_if1);
    
    uvm_top.finish_on_completion = 1;
    
    //    run_test("my_test");  // Original test
    run_test("my_test2");       // Alternative test
  end

endmodule: top
