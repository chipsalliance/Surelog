interface my_interface(
  input clock,
  output select,
  output [3:0] data);
  
  clocking cb @(posedge clock);
    output select, data;
  endclocking
endinterface

import uvm_pkg::*;
`include "uvm_macros.svh"

// The transaction that driver expects to receive
class my_transaction extends uvm_sequence_item;
  int data;
endclass

// Simple driver.
// When driver receives a transaction, it drives the data on the bus
// for one cycle, and then drivers idle for one cycle.
class my_driver extends uvm_driver #(my_transaction);

  virtual my_interface _if;

  `uvm_component_utils(my_driver)

  function new (string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  task run_phase(uvm_phase phase);
    forever begin
      my_transaction tr = new();
      seq_item_port.get_next_item(tr);
      
      // Drive transaction on the bus
      @(_if.cb);
      _if.cb.select <= 1;
      _if.cb.data <= tr.data;
      // Drive idle
      @(_if.cb);
      _if.cb.select <= 0;
      _if.cb.data <= 0;

      seq_item_port.item_done();
    end
  endtask

endclass // my_driver
