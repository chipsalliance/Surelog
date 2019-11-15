
`include "svunit_defines.svh"

import svunit_pkg::*;

module apb_slave_unit_test;

  string name = "apb_slave_ut";
  svunit_testcase svunit_ut;

  logic [7:0] addr;
  logic [31:0] data, rdata;


  //===================================
  // This is the UUT that we're 
  // running the Unit Tests on
  //===================================
  reg         clk;
  reg         rst_n;
  reg [7:0]   paddr;
  reg         pwrite;
  reg         psel;
  reg         penable;
  reg [31:0]  pwdata;
  wire [31:0] prdata;

  // clk generator
  initial begin
    clk = 0;
    forever begin
      #5 clk = ~clk;
    end
  end

  apb_slave my_apb_slave(.*);

  //===================================
  // Build
  //===================================
  function void build();
    svunit_ut = new(name);
  endfunction


  //===================================
  // Setup for running the Unit Tests
  //===================================
  task setup();
    svunit_ut.setup();

    //-----------------------------------------
    // move the bus into the IDLE state
    // before each test
    //-----------------------------------------
    idle();

    //-----------------------------
    // then do a reset for the uut
    //-----------------------------
    rst_n = 0;
    repeat (8) @(posedge clk);
    rst_n = 1;
  endtask


  //===================================
  // Here we deconstruct anything we 
  // need after running the Unit Tests
  //===================================
  task teardown();
    svunit_ut.teardown();
    /* Place Teardown Code Here */
  endtask


  //===================================
  // All tests are defined between the
  // SVUNIT_TESTS_BEGIN/END macros
  //
  // Each individual test must be
  // defined between `SVTEST(_NAME_)
  // `SVTEST_END
  //
  // i.e.
  //   `SVTEST(mytest)
  //     <test code>
  //   `SVTEST_END
  //===================================
  `SVUNIT_TESTS_BEGIN


  //************************************************************
  // Test:
  //   single_write_then_read
  //
  // Desc:
  //   do a write then a read at the same address
  //************************************************************
  `SVTEST(single_write_then_read)
    addr = 'h32;
    data = 'h61;

    write(addr, data);
    read(addr, rdata);
    `FAIL_IF(data !== rdata);
  `SVTEST_END


  //************************************************************
  // Test:
  //   write_wo_psel
  //
  // Desc:
  //   do a write then a read at the same address but insert a
  //   write without psel asserted during setup to ensure mem
  //   isn't corrupted by a protocol error.
  //************************************************************
  `SVTEST(write_wo_psel)
    addr = 'h0;
    data = 'hffff_ffff;

    write(addr, data);
    write(addr, 'hff, 0, 0);
    read(addr, rdata);
    `FAIL_IF(data !== rdata);
  `SVTEST_END


  //************************************************************
  // Test:
  //   write_wo_write
  //
  // Desc:
  //   do a write then a read at the same address but insert a
  //   write without pwrite asserted during setup to ensure mem
  //   isn't corrupted by a protocol error.
  //************************************************************
  `SVTEST(write_wo_write)
    addr = 'h10;
    data = 'h99;

    write(addr, data);
    write(addr, 'hff, 0, 1, 0);
    read(addr, rdata);
    `FAIL_IF(data !== rdata);
  `SVTEST_END


  //************************************************************
  // Test:
  //   _2_writes_then_2_reads
  //
  // Desc:
  //   Do back-to-back writes then back-to-back reads
  //************************************************************
  `SVTEST(_2_writes_then_2_reads)
    addr = 'hfe;
    data = 'h31;

    write(addr, data, 1);
    write(addr+1, data+1, 1);
    read(addr, rdata, 1);
    `FAIL_IF(data !== rdata);
    read(addr+1, rdata, 1);
    `FAIL_IF(data+1 !== rdata);

  `SVTEST_END


  `SVUNIT_TESTS_END


  // write ()
  //
  // Simple write method used in the unit tests.
  // Includes options for back-to-back writes and protocol
  // errors on the psel and pwrite.
  task write(logic [7:0] addr,
             logic [31:0] data,
             logic back2back = 0,
             logic setup_psel = 1,
             logic setup_pwrite = 1);

    // if !back2back, insert an idle cycle before the write
    if (!back2back) begin
      @(negedge clk);
      psel = 0;
      penable = 0;
    end

    // this is the SETUP state where the psel,
    // pwrite, paddr and pdata are set
    //
    // NOTE:
    //   setup_psel == 0 for protocol errors on the psel
    //   setup_pwrite == 0 for protocol errors on the pwrite
    @(negedge clk);
    psel = setup_psel;
    pwrite = setup_pwrite;
    paddr = addr;
    pwdata = data;
    penable = 0;

    // this is the ENABLE state where the penable is asserted
    @(negedge clk);
    pwrite = 1;
    penable = 1;
    psel = 1;
  endtask


  // read ()
  //
  // Simple read method used in the unit tests.
  // Includes options for back-to-back reads.
  //
  task read(logic [7:0] addr, output logic [31:0] data,
  	        input logic back2back = 0);

    // if !back2back, insert an idle cycle before the read
    if (!back2back) begin
      @(negedge clk);
      psel = 0;
      penable = 0;
    end

    // this is the SETUP state where the psel, pwrite and paddr
    @(negedge clk);
    psel = 1;
    paddr = addr;
    penable = 0;
    pwrite = 0;

    // this is the ENABLE state where the penable is asserted
    @(negedge clk);
    penable = 1;

    // the prdata should be flopped after the subsequent posedge
    @(posedge clk);
    #1 data = prdata;
  endtask

  // idle ()
  //
  // Clear the all the inputs to the uut (i.e. move to the IDLE state)
  task idle();
    @(negedge clk);
    psel = 0;
    penable = 0;
    pwrite = 0;
    paddr = 0;
    pwdata = 0;
  endtask
  
  initial begin
    // Dump waves
    $dumpvars(0, apb_slave_unit_test);
  end

endmodule
