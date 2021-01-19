package flash_ctrl_reg_pkg;

typedef struct packed {
    struct packed {
      logic        q;
    } en;
    struct packed {
      logic        q;
    } rd_en;
  } flash_ctrl_reg2hw_mp_region_cfg_mreg_t;
   
endpackage   


package flash_ctrl_pkg;
   
 typedef flash_ctrl_reg_pkg::flash_ctrl_reg2hw_mp_region_cfg_mreg_t mp_region_cfg_t;

endpackage   

module top();
  import flash_ctrl_pkg::*;

   mp_region_cfg_t region_cfg;
   
   
endmodule // top

