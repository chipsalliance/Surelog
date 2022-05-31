package pack;
typedef struct packed
{
    logic stall;
    logic clear;
} PipelineControll;

endpackage

import pack::*;

interface ControllerIF(
   input
       logic clk,
       logic rst
   );

   PipelineControll backEnd;

   modport BypassNetwork(
      input
          backEnd
      );

endinterface



module BypassNetwork( 
    ControllerIF.BypassNetwork ctrl
);

 assign o = ctrl.backEnd;


endmodule // BypassNetwork
