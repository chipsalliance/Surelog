`include "svunit_defines.svh"
import svunit_pkg::*;

// SVUnit module must end with '_unit_test'
module my_scoreboard_unit_test;

  string name = "my_scoreboard_ut";
  svunit_testcase svunit_ut;

  // This is the UUT that we're 
  // running the Unit Tests on
  my_scoreboard dut;
  
  // The analysis port we use to communicate with scoreboard.
  uvm_analysis_port #(int) m_ap;
  
  // Build - runs once
  function void build();
    svunit_ut = new(name);
    dut = my_scoreboard::type_id::create("dut", null);
    
    // Connect analysis port to scoreboard
    m_ap = new("ap", null);
    m_ap.connect(dut.m_imp);
    m_ap.resolve_bindings();
  endfunction

  // Setup before each test
  task setup();
    svunit_ut.setup();
    // Clear the internals of scoreboard
    dut.internal_state = 0;
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

  // Test that internal state of scoreboard updated correctly
  // when a write came in on analysis port.
  `SVTEST(one_write)
    `INFO("Running one_write");
    m_ap.write(4);
    `FAIL_UNLESS_EQUAL(4, dut.internal_state);
  `SVTEST_END

  // Test that internal state of scoreboard updated correctly
  // when multiple writes come in on analysis port.
  `SVTEST(multiple_write)
    m_ap.write(4);
    m_ap.write(0);
    m_ap.write(-2);
    `FAIL_UNLESS_EQUAL(2, dut.internal_state);
  `SVTEST_END

  // Test that fails on purpose for demo purposes.
  `SVTEST(example_failure)
    `FAIL_UNLESS_EQUAL(2, dut.internal_state);
  `SVTEST_END

  `SVUNIT_TESTS_END

endmodule

