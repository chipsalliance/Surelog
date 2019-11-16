//
// Template for VMM-compliant verification environment
//
// [filename]  tb_env
//


`ifndef TB_ENV__SV
`define TB_ENV__SV

`include "vmm.sv"

// ToDo: Add additional required `include directives

class test_cfg;

   // ToDo: Define test configuration parameters (e.g. how long to run)

   function new();
   endfunction: new

   function string psdisplay(string prefix = "");
   endfunction
endclass: test_cfg


class scoreboard;
   test_cfg cfg;
   vmm_log  log;

   function new(test_cfg cfg);
      this.cfg = cfg;
      this.log = new("Scoreboard", "");
   endfunction: new

endclass


class tb_env extends vmm_env;
   test_cfg cfg;

   // ToDo: Declare transactor instances as data members

   scoreboard sb;

   function new();
      super.new();
      this.cfg = new;
      $timeformat(-9, 0, "ns", 1);
   endfunction: new

   virtual function void gen_cfg();
      super.gen_cfg();

      if (!this.cfg.randomize()) begin
         `vmm_fatal(log, "Failed to randomize test configuration");
      end
   endfunction: gen_cfg


   virtual function void build();
      super.build();

      `vmm_note(this.log, this.cfg.psdisplay());

      // ToDo: Instantiate transactors, using XMRs to access interface instances
      // ToDo: Register any required callbacks

      this.sb = new(this.cfg);

      // ToDo: Start transactors needed to configure the DUT
   endfunction: build


   virtual task reset_dut();
      super.reset_dut();

      // ToDo: Apply hardware reset to DUT
   endtask: reset_dut

      
   virtual task cfg_dut();
      super.cfg_dut();

      // ToDo: Configure DUT
   endtask: cfg_dut


   virtual task start();
      super.start();

      // ToDo: Start all transactors
   endtask: start


   virtual task wait_for_end();
      super.wait_for_end();

      // ToDo: Figure out when it is time to end the test
   endtask: wait_for_end


   virtual task stop();
      super.stop();

      // ToDo: Stop all generators

      // ToDo: Let the DUT drain of all pending data
   endtask: stop


   virtual task cleanup();
      super.cleanup();

      // ToDo: check that nothing was lost
   endtask: cleanup
endclass

`endif
