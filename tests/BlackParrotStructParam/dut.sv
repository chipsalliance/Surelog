package bp_common_aviary_pkg;
  
  localparam max_cfgs    = 1;

typedef struct packed
  {
    integer cc_x_dim;
  }  bp_proc_param_s;

  localparam bp_proc_param_s bp_default_cfg_p =
    '{
      cc_x_dim : 1
      };

 localparam bp_proc_param_s bp_unicore_cfg_p = bp_default_cfg_p;

  localparam bp_proc_param_s bp_multicore_cce_ucode_half_override_p =
    '{
      default : "inv"
      };

 localparam bp_proc_param_s bp_multicore_1_cce_ucode_cfg_p     =                                                       
      '{  
    cc_x_dim: (bp_multicore_cce_ucode_half_override_p
                        .cc_x_dim == "inv") 
                  ? bp_unicore_cfg_p 
                        .cc_x_dim           
                  : bp_unicore_cfg_p 
                        .cc_x_dim          
      };

localparam bp_proc_param_s bp_multicore_cce_ucode_half_cfg_p    =                                                       
      '{ 
    cc_x_dim: (bp_multicore_cce_ucode_half_override_p
                        .cc_x_dim == "inv") 
                  ? bp_multicore_1_cce_ucode_cfg_p
                        .cc_x_dim           
                  : bp_multicore_cce_ucode_half_override_p
                        .cc_x_dim          
        };

 parameter bp_proc_param_s [max_cfgs:0] all_cfgs_gp =
  {
    // Various testing configs
    bp_multicore_cce_ucode_half_cfg_p
  };

 typedef enum bit [max_cfgs:0]
  {
    e_bp_default_cfg                       = 0
  } bp_params_e;

endpackage

module top import bp_common_aviary_pkg::*; #(
  parameter bp_params_e bp_params_p = e_bp_default_cfg
, localparam bp_proc_param_s proc_param_lp = all_cfgs_gp[bp_params_p]   
, localparam cc_x_dim_p  = proc_param_lp.cc_x_dim ) ();                                               

 logic [cc_x_dim_p-1:0] aa;

 if (cc_x_dim_p == 1) begin
    OK ok();    
 end
   
endmodule


