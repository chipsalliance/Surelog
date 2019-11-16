`include "svunit_defines.svh"
import uvm_pkg::*;
`include "uvm_macros.svh"
import svunit_pkg::*;

// Mock sequencer for sending transactions to the driver
class mock_sequencer extends uvm_sequencer #(my_transaction);
  `uvm_sequencer_utils(mock_sequencer)
  function new(input string name, uvm_component parent=null);
     super.new(name, parent);
  endfunction : new

  // Check whether item_done was just called for the specified
  // transaction_id.
  // Return 1 if transaction_id matches, 0 otherwise.
  function bit check_item_done(int transaction_id);
    return transaction_id === m_wait_for_item_transaction_id;
  endfunction
endclass

// Mock sequence to run on the mock sequencer.
class mock_sequence extends uvm_sequence #(my_transaction);
  `uvm_sequence_utils(mock_sequence, mock_sequencer)
endclass

// SVUnit module must end with '_unit_test'
module my_driver_unit_test;

  string name = "my_driver_ut";
  svunit_testcase svunit_ut;

  // This is the UUT that we're 
  // running the Unit Tests on
  my_driver dut;
  
  // The mock sequencer
  mock_sequencer sequencer;

  // Create the interface
  logic clock;
  wire select;
  wire [3:0] data;
  my_interface my_interface(.*);
  
  // Build - runs once
  function void build();
    svunit_ut = new(name);
    dut = my_driver::type_id::create("dut", null);
    dut._if = my_interface;
    
    // Connect transaction port to the driver
    sequencer = mock_sequencer::type_id::create("sequencer", null);
    dut.seq_item_port.connect(sequencer.seq_item_export);
    dut.seq_item_port.resolve_bindings();
  endfunction

  // Setup before each test
  task setup();
    svunit_ut.setup();
    // Clear the bus
    clock = 0;
    my_interface.cb.select <= 0;
    my_interface.cb.data <= 0;
    repeat (2) toggle_clock();
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

  // Test that driver sends one packet
  `SVTEST(one_packet)
    mock_sequence m_seq;
    my_transaction req;
    int data_to_send = 3;
    req = new();
    req.data = data_to_send;
    m_seq = new();
  
    // Run driver
    fork: run
      dut.run_phase(null);
      begin
        sequencer.wait_for_grant(m_seq);
        sequencer.send_request(m_seq, req);
      end
    join_none

    toggle_clock();

    // Check that correct pins were driven
    `FAIL_UNLESS(select === 1'b1);
    `FAIL_UNLESS(data === data_to_send);
    toggle_clock();
    `FAIL_UNLESS(select === 1'b0);
    `FAIL_UNLESS(data === 0);

    // Make sure item_done is sent back
    `FAIL_UNLESS(sequencer.check_item_done(req.get_transaction_id()));

    // Stop driver
    disable run;

  `SVTEST_END

  // Test that driver does not drive pins without a transaction
  `SVTEST(no_packet)
    // Run driver
    fork: run
      dut.run_phase(null);
    join_none

    // Make sure the pins stay at their default values.
    repeat (10) begin
      toggle_clock();
      `FAIL_UNLESS(select === 1'b0);
      `FAIL_UNLESS(data === 0);
    end

    // Set the pins to different values
    my_interface.cb.select <= 1'bz;
    my_interface.cb.data <= 4'hz;
    // And make sure they stay that way
    repeat (10) begin
      toggle_clock();
      `FAIL_UNLESS(select === 1'bz);
      `FAIL_UNLESS(data === 4'hz);
    end
  
    // Stop driver
    disable run;
  `SVTEST_END
   
  `SVUNIT_TESTS_END
  
  task toggle_clock();
    repeat (2) #5 clock = ~clock;
  endtask // toggle_clock
  
  initial begin
    // Dump waves
    $dumpvars(0, my_driver_unit_test);
  end

endmodule

