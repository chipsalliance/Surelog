#include "Vsyn_tb.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

double sc_time_stamp() {
  return 0;
} 

int main(int argc, char** argv, char** env) {
  Verilated::commandArgs(argc, argv);
  Vsyn_tb* top = new Vsyn_tb;
  // init trace dump
  Verilated::traceEverOn(true);
  Verilated::assertOn(true);
  VerilatedVcdC* tfp = new VerilatedVcdC;

  top->clk = 0;
  top->trace(tfp, 99);
  tfp->open("syn_tb.vcd");
  
  // run simulation for 20 clock periods
  // Only generate the clock in C,
  // the testbench is in Verilog
  for(int i = 0; i < 20; i++)
    {
      for(int clk = 0; clk < 2; ++clk)
	{
	  top->eval();
	  tfp->dump((2 * i) + clk);
	  top->clk = !top->clk;
	}
    }
  tfp->close();
  delete top;
  exit(0);
}
