//
// Template for VMM-compliant interface
//
// <IF>        Name of physical bus
//

`ifndef IF__SV
`define IF__SV

`include "vmm.sv"


// ToDo: One clock per clock domain
  
interface IF(input bit ck1,
             input bit ck2);

   // ToDo: Define default setup & hold times

   parameter setup_time = 5/*ns*/;
   parameter hold_time  = 3/*ns*/;

   // ToDo: Define synchronous and asynchronous signals as wires

   wire [15:0] sync_txd;
   wire [15:0] sync_rxd;
   wire [15:0] sync_dat;

   logic       async_en;
   logic       async_rdy;


   // ToDo: Define one clocking block per clock domain
   //       with synchronous signal direction from a
   //       master perspective

   clocking mck1 @(posedge ck1);
      default input #setup_time output #hold_time;
      output sync_txd;
      inout  sync_dat;
   endclocking: mck1

   clocking mck2 @(posedge ck2);
      default input #setup_time output #hold_time;
      input sync_rxd;
   endclocking: mck2


   // ToDo: Define one clocking block per clock domain
   //       with synchronous signal direction from a
   //       slave perspective

   clocking sck1 @(posedge ck1);
      default input #setup_time output #hold_time;
      input sync_txd;
      inout sync_dat;
   endclocking: sck1

   clocking sck2 @(posedge ck2);
      default input #setup_time output #hold_time;
      output sync_rxd;
   endclocking: sck2


   // ToDo: Define one clocking block per clock domain
   //       with synchronous signal direction from a
   //       monitor perspective

   clocking pck1 @(posedge ck1);
      default input #setup_time output #hold_time;
      input sync_txd;
      input sync_dat;
   endclocking: pck1

   clocking pck2 @(posedge ck2);
      default input #setup_time output #hold_time;
      input sync_rxd;
   endclocking: pck2


   // ToDo: Define a modport for each master, slave and
   //       monitor, with appropriate asynchronous signal
   //       directions and clocking blocks

   modport master(clocking mck1,
                  clocking mck2,
                  output async_en,
                  input  async_rdy);

   modport slave(clocking sck1,
                 clocking sck2,
                 input  async_en,
                 output async_rdy);

   modport passive(clocking pck1,
                   clocking pck2,
                   input async_en,
                   input async_rdy);
endinterface: IF


`endif
