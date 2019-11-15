////////////////////////////////////////////////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////s           www.testbench.in           s////
////s                                      s////
////s              UVM Tutorial            s////
////s                                      s////
////s            gopi@testbench.in          s////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
//////////////////////////////////////////////// 

`ifndef GUARD_INTERFACE
`define GUARD_INTERFACE


//////////////////////////////////////////
// Interface declaration for the memory///
//////////////////////////////////////////

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

////////////////////////////////////////////
// Interface for the input side of switch.//
// Reset signal is also passed hear.      //
////////////////////////////////////////////
interface input_interface(input bit clock);

    parameter setup_time = 5ns;
    parameter hold_time = 3ns;

    wire           data_status;
    wire     [7:0] data_in;
    reg            reset; 

    clocking cb@(posedge clock);
       default input #setup_time output #hold_time;
       output    data_status;
       output    data_in;
    endclocking:cb
    
    modport IP(clocking cb,output reset,input clock);
  
endinterface:input_interface

/////////////////////////////////////////////////
// Interface for the output side of the switch.//
// output_interface is for only one output port//
/////////////////////////////////////////////////

interface output_interface(input bit clock);

    parameter setup_time = 5ns;
    parameter hold_time = 3ns;

    wire    [7:0] data_out;
    wire    ready;
    wire    read;
    
    clocking cb@(posedge clock);
      default input #setup_time output #hold_time;
      input     data_out;
      input     ready;
      output    read;
    endclocking:cb
    
    modport OP(clocking cb,input clock);

endinterface:output_interface

//////////////////////////////////////////////////

`endif 
