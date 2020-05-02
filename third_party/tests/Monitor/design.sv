interface my_interface(
  input wire clock,
  input wire select,
  input wire [3:0] data);
  
  clocking cb @(posedge clock);
    input select, data;
  endclocking
endinterface

import uvm_pkg::*;
`include "uvm_macros.svh"

// Simple monitor.
// When select is high, the monitor writes data to analysis port.
class my_monitor extends uvm_monitor;

  virtual my_interface _if;

  // The analysis port we use to communicate with scoreboard.
  uvm_analysis_port #(int) m_ap;
  
  `uvm_component_utils(my_monitor)

  function new (string name, uvm_component parent = null);
    super.new(name, parent);
    m_ap = new("ap", this);
  endfunction
  
  task run_phase(uvm_phase phase);
    forever begin
      @_if.cb;
      if (_if.cb.select) begin
        int pkt = _if.cb.data;
        m_ap.write(pkt);
      end
    end
  endtask

endclass
