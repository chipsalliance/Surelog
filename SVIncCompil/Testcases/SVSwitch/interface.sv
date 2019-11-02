////////////////////////////////////////////////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////s           www.testbench.in           s////
////s                                      s////
////s        SystemVerilog Tutorial        s////
////s           gopi@testbench.in          s////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////////////////////////////////////////////////
`ifndef GUARD_INTERFACE
`define GUARD_INTERFACE

//////////////////////////////////////////
// Interface declaration for the memory///
//////////////////////////////////////////

interface mem_interface(input bit clock);
  logic [7:0] mem_data;
  logic [1:0] mem_add;
  logic       mem_en;
  logic       mem_rd_wr;
  
  clocking cb@(posedge clock);
     default input #1 output #1;
     output     mem_data;
     output      mem_add;
     output mem_en;
     output mem_rd_wr;
  endclocking
  
  modport MEM(clocking cb,input clock);

endinterface

////////////////////////////////////////////
// Interface for the input side of switch.//
// Reset signal is also passed hear.      //
////////////////////////////////////////////
interface input_interface(input bit clock);
  logic           data_status;
  logic     [7:0] data_in;
  logic           reset; 

  clocking cb@(posedge clock);
     default input #1 output #1;
     output    data_status;
     output    data_in;
  endclocking
  
  modport IP(clocking cb,output reset,input clock);
  
endinterface

/////////////////////////////////////////////////
// Interface for the output side of the switch.//
// output_interface is for only one output port//
/////////////////////////////////////////////////

interface output_interface(input bit clock);
  logic    [7:0] data_out;
  logic    ready;
  logic    read;
  
  clocking cb@(posedge clock);
    default input #1 output #1;
    input     data_out;
    input     ready;
    output    read;
  endclocking
  
  modport OP(clocking cb,input clock);

endinterface


//////////////////////////////////////////////////

`endif 
