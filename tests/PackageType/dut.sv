package bp_common_aviary_pkg;
  
typedef struct packed
{
  integer num_core;
  integer num_cce;
}  bp_proc_param_s;

  // Suitably high enough to not run out of configs.
  localparam max_cfgs    = 128;
  localparam lg_max_cfgs = $clog2(max_cfgs);

  localparam bp_proc_param_s bp_inv_cfg_p = 
    '{default: "inv"};


  /* verilator lint_off WIDTH */     
  parameter bp_proc_param_s [max_cfgs-1:0] all_cfgs_gp =
  {
   bp_inv_cfg_p
  };
  /* verilator lint_on WIDTH */

endpackage
