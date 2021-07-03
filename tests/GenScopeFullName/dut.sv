module dut();
   logic [1:0] a;

   for(genvar i = 0; i < 1; i++) begin : gen_modules
      ibex_counter module_in_genscope(.b(a[i]));
      //assign a[i] = 0;

   end // block: gen_modules

endmodule // dut

module ibex_counter(input logic b);

endmodule // ibex_counter
