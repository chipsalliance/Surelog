module dut ();
        // CPU control register fields
        typedef struct packed {
          logic [2:0]  dummy_instr_mask;
          logic        dummy_instr_en;
          logic        data_ind_timing;
          logic        icache_enable;
        } cpu_ctrl_t;
        cpu_ctrl_t   cpuctrl_wdata;
        logic [31:0] csr_wdata_int;
        assign cpuctrl_wdata = cpu_ctrl_t'(csr_wdata_int[$bits(cpu_ctrl_t)-1:0]);
endmodule
