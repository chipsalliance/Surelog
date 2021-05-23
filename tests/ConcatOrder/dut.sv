package bp_common_pkg;
  localparam max_cfgs    = 2;
  localparam lg_max_cfgs = ( ((max_cfgs)==1) ? 1 : $clog2((max_cfgs)));

 typedef struct packed
  { 
    integer unsigned cce_ucode;
  }  bp_proc_param_s;

   localparam bp_proc_param_s bp_multicore_1_cce_ucode_cfg_p=                                                     
      '{    cce_ucode: 1     };
   
parameter bp_proc_param_s [max_cfgs-1:0] all_cfgs_gp =
  {
    bp_multicore_1_cce_ucode_cfg_p
    ,bp_default_cfg_p
  };
 
  typedef enum bit [lg_max_cfgs-1:0]
  {
    e_bp_multicore_1_cce_ucode_cfg                 = 1
    ,e_bp_default_cfg                               = 0
  } bp_params_e;

localparam bp_proc_param_s bp_default_cfg_p =
    '{
       cce_ucode            : 0  
      };

localparam bp_proc_param_s bp_unicore_cfg_p = bp_default_cfg_p;

endpackage


module GOOD ();

endmodule
   
 module testbench
 import bp_common_pkg::*;
 #(parameter bp_params_e bp_params_p = e_bp_multicore_1_cce_ucode_cfg 
   
    , localparam bp_proc_param_s proc_param_lp = all_cfgs_gp[bp_params_p]                       
    , localparam cce_ucode_p                = proc_param_lp.cce_ucode
)
  ();

 if (cce_ucode_p == 1) begin 
     GOOD good();
 end else begin
     BAD bad();
 end

 endmodule

