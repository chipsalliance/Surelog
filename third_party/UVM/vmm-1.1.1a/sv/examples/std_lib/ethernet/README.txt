

			 Ethernet/MII VIP Example


To run the VIP-only tests:

   % make test_mii
   ...
   Simulation PASSED on /./ (/./) at 206575ns (0 warnings, 0 demoted errors & 0 demoted warnings)
   $finish at simulation time 206575ns

   % make test_mac
   ...


The MII example test has the following structure:

 3 Frames -> MII MAC ->    MII    -> MII PHY ->
          <-  Side   <- Interface <-  Side   <- 3 Frames



The MAC example test has the following structure:

                                       MAC
                                     Monitor
                                       ^ ^
                                       | |
                                       MII
                                     Monitor
                                       ^ ^
                                       | |
 3 Frames -> Ethernet -> MII MAC ->    MII    -> MII PHY -> Ethernet ->
          <-   MAC    <-  Side   <- Interface <-  Side   <-   MAC    <- 3 Frames



Files:

   eth_frame.sv			Ethernet Frame Descriptor
   eth_frame_gen.sv		Atomic Frame Generator
   eth_frame_scenario_gen.sv	Scenario Frame Generator
   ethernet.sv			Top-level File for Ethernet VIP
   mac.sv			MAC-layer Transactor
   mii.sv			Top-level File for MII VIP
   mii_env.sv			Environment for MII-only Test
   mii_if.sv			MII Interface Declaration
   mii_mac.sv			MAC-side MII Transactor
   mii_mac_bfm.sv		Module Encapsulated MAC-side MII Transactor
   mii_mon.sv			MII Monitor
   mii_phy.sv			PHY-side MII Transactor
   mii_sva_checker.sv		MII Checker
   mii_sva_types.sv
   pls.sv			MAC Layer Notification Interface
   test_mac.sv			MAC-layer VIP-only Testcase
   test_mii.sv			MII-Layer VIP-only Testcase
   top.sv			MII Interface Instance
   utils.sv			CRC and Packign Utility Routines
