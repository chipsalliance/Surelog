interface intf;
   parameter int unsigned Depth = 4;
   int                    o;

   function automatic int get2();
         return 1;
      endfunction 

   if (Depth > 2) begin : gen_block
      function automatic int get3();
         return 1;
      endfunction 

      assign o = get3();
   end : gen_block
   else
     assign o = 0;
endinterface


module top;
   parameter int unsigned Depth = 4;
   int                    o;

   function automatic int get4();
         return 1;
      endfunction 
  intf interf();
   if (Depth > 2) begin : gen_block
      function automatic int get1();
         return 1;
      endfunction // get1

      assign o = get1();
   end : gen_block
   else
     assign o = 0;


endmodule
