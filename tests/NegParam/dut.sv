module top();
 localparam dram_base_addr_gp         = 40'h00_8000_0000;
 
 localparam bp_proc_param_s bp_default_cfg_p =
    '{
      boot_pc       : dram_base_addr_gp
    };

endmodule
