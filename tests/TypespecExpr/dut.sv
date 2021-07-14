module Mod1 #(parameter logic [31:0] PARAM = '0) (output logic [31:0] x);
   assign x = PARAM;
endmodule

module Mod2;
   typedef struct packed { logic[31:0] x; } Struct;
   parameter Struct STRUCT = '{ x: '0 };
   logic[31:0] x;
   Mod1 #(.PARAM(STRUCT)) mod1(.x(x));
endmodule

