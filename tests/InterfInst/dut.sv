
interface sim_sram_if;   
   int start_addr;
endinterface // sim_sram_if

module dut(sim_sram_if ss_if, output int a);
   assign a = ss_if.start_addr;
endmodule // dut

module top(output int o);
   sim_sram_if u_sim_sram_if();
   assign u_sim_sram_if.start_addr = 32'h1234;
   dut u_dut(.ss_if(u_sim_sram_if), .a(o));
endmodule // top
