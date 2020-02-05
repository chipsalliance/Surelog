import uvm_pkg::*;
`include "uvm_macros.svh"
`include "svunit_defines.svh"
import svaunit_pkg::*;
import svunit_pkg::*;

// Mock scoreboard for receiving analysis port writes
class mock_scoreboard extends uvm_scoreboard;

  int write_count;
  int last_pkt;
  uvm_analysis_imp #(int, mock_scoreboard) m_imp;
  
  `uvm_component_utils(mock_scoreboard)
  
  function new(string name, uvm_component parent);
    super.new(name, parent);
    m_imp = new("imp", this);
  endfunction
  
  // Mock write method that simply captures the pkt
  function void write(int pkt);
    write_count++;
    last_pkt = pkt;
  endfunction

endclass

// SVUnit module must end with '_unit_test'
module my_monitor_unit_test;

  string name = "my_monitor_ut";
  svunit_testcase svunit_ut;

  // This is the UUT that we're 
  // running the Unit Tests on
  my_monitor dut;
  
  // The mock scoreboard
  mock_scoreboard scoreboard;

  // Create the interface
  logic clock;
  logic select;
  logic [3:0] data;
  my_interface my_interface(.*);
  
  // Build - runs once
  function void build();
    svunit_ut = new(name);
    dut = my_monitor::type_id::create("dut", null);
    
    // Connect analysis port to mock scoreboard
    scoreboard = mock_scoreboard::type_id::create("scoreboard", null);
    dut.m_ap.connect(scoreboard.m_imp);
    dut.m_ap.resolve_bindings();
    dut._if = my_interface;
  endfunction

  // Setup before each test
  task setup();
    svunit_ut.setup();
    // Clear the internals of scoreboard
    scoreboard.write_count = 0;
    clock = 0;
    select = 0;
    data = 0;
    #1;
  endtask

  // Teardown after each test
  task teardown();
    svunit_ut.teardown();
  endtask

  // All tests are defined between the
  // SVUNIT_TESTS_BEGIN/END macros
  //
  // Each individual test must be
  // defined between `SVTEST(_NAME_) and `SVTEST_END
  `SVUNIT_TESTS_BEGIN

  // Test that monitor sends one packet
  `SVTEST(one_packet)
    // Run monitor
    fork: run
      dut.run_phase(null);
    join_none

    // Toggle interface pins
    select = 1;
    data = 3;
    toggle_clock();

    // Stop monitor
    disable run;
    
    // Check that correct packet was received
    `FAIL_UNLESS_EQUAL(1, scoreboard.write_count);
    `FAIL_UNLESS_EQUAL(3, scoreboard.last_pkt);
  `SVTEST_END

  // Test that monitor sends no packets when select is off
  `SVTEST(select_off)
    // Run monitor
    fork: run
      dut.run_phase(null);
    join_none

    // Toggle interface pins
    data = 3;
    repeat (3) toggle_clock();

    // Stop monitor
    disable run;
    
    // Check that no packets were received
    `FAIL_IF(scoreboard.write_count);
  `SVTEST_END

  `SVUNIT_TESTS_END
  
  task toggle_clock();
    repeat (2) #5 clock = ~clock;
  endtask
  
  initial begin
    // Dump waves
    $dumpvars(0, my_monitor_unit_test);
  end

endmodule

