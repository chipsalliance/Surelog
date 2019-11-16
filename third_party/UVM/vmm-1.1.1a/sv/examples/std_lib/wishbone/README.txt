

			 Wishbone VIP Example


To run the VIP-only test:

   % make
   ...
   Simulation PASSED on /./ (/./) at 12920ns (0 warnings, 0 demoted errors & 0 demoted warnings)
   $finish at simulation time 12920ns



The example test has the following structure:

 100 read & write <-> Wishbone <-> Wishbone  <-> Wishbone ->   RAM
                       Master      Interface      Slave   <- Response



Files:

	config.sv		Configuration Descriptor
	cycle.sv		Transaction Descriptor
	master.sv		Master Transactor
	master_chk.sv		Master Protocol Checker
	slave.sv		Slave Transactor
	slave_chk.sv		Slave Protocol Checker
	test.sv			VIP-only Test
	wb_chk_coverage.sv	Protocol Checker Coverage Model
	wb_if.sv		Interface Declaration
	wishbone.sv		Top-level VIP file
