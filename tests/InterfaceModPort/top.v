interface mem_interface(input bit clock);

   parameter setup_time = 5ns;
   parameter hold_time = 3ns;

   wire [7:0] mem_data;
   wire [1:0] mem_add;
   wire       mem_en;
   wire       mem_rd_wr;
   
   clocking cb@(posedge clock);
      default input #setup_time output #hold_time;
      output     mem_data;
      output      mem_add;
      output mem_en;
      output mem_rd_wr;
   endclocking:cb
   
   modport MEM(clocking cb,input clock);

endinterface :mem_interface

//+++++++++++++++++++++++++++++++++++++++++++++++++
// Define the interface
//+++++++++++++++++++++++++++++++++++++++++++++++++
interface mem_if (input wire clk);
  logic        reset;
  logic        we_sys;
  logic        cmd_valid_sys;
  logic        ready_sys;
  logic  [7:0] data_sys;
  logic  [7:0] addr_sys;
  logic        we_mem;
  logic        ce_mem;
  logic  [7:0] datao_mem;
  logic  [7:0] datai_mem;
  logic  [7:0] addr_mem;
  //=================================================
  // Modport for System interface 
  //=================================================
  modport  system (input clk,reset,we_sys, cmd_valid_sys,
                   addr_sys, datao_mem, 
                   output we_mem, ce_mem, addr_mem, 
                   datai_mem, ready_sys, ref data_sys);
  //=================================================
  // Modport for memory interface 
  //=================================================
  modport  memory (input clk,reset,we_mem, ce_mem,
                   addr_mem, datai_mem, output datao_mem);
  //=================================================
  // Modport for testbench 
  //=================================================
  modport  tb (input clk, ready_sys, 
               output reset,we_sys, cmd_valid_sys, addr_sys, 
              ref data_sys);

endinterface

//+++++++++++++++++++++++++++++++++++++++++++++++++
//  Memory Model 
//+++++++++++++++++++++++++++++++++++++++++++++++++
module memory_model (mem_if.memory mif);
// Memory array
logic [7:0] mem [0:255];

//=================================================
// Write Logic
//=================================================
always @ (posedge mif.clk)
 if (mif.ce_mem && mif.we_mem) begin
   mem[mif.addr_mem] <= mif.datai_mem;
 end

//=================================================
// Read Logic
//=================================================
always @ (posedge mif.clk)
 if (mif.ce_mem && ~mif.we_mem)  begin
   mif.datao_mem <= mem[mif.addr_mem];
 end

endmodule

//+++++++++++++++++++++++++++++++++++++++++++++++++
//  Memory Controller
//+++++++++++++++++++++++++++++++++++++++++++++++++
module memory_ctrl (mem_if.system sif);

typedef  enum {IDLE,WRITE,READ,DONE} fsm_t;

fsm_t state;


endmodule

//+++++++++++++++++++++++++++++++++++++++++++++++++
// Test  program
//+++++++++++++++++++++++++++++++++++++++++++++++++
program test(mem_if.tb tif);

   initial begin
      tif.reset <= 1;
 
      #10 $finish;
   end

endprogram

//+++++++++++++++++++++++++++++++++++++++++++++++++
//  Testbench
//+++++++++++++++++++++++++++++++++++++++++++++++++
module interface_modports();

logic clk = 0;
always #10 clk++;
//=================================================
// Instianciate Interface and DUT 
//=================================================
mem_if miff(clk);
memory_ctrl U_ctrl(miff);
memory_model U_model(miff);
test   U_test(miff);

endmodule
