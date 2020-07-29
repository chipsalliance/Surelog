package flash_ctrl_reg_pkg;

  // Param list
  parameter int NBanks = 2;
  parameter int NumRegions = 8;

  typedef struct packed {
    struct packed {
      logic        q;
    } en;
    struct packed {
      logic        q;
    } rd_en;
    struct packed {
      logic        q;
    } prog_en;
    struct packed {
      logic        q;
    } erase_en;
    struct packed {
      logic [8:0]  q;
    } base;
    struct packed {
      logic [8:0]  q;
    } size;
  } flash_ctrl_reg2hw_mp_region_cfg_mreg_t;

  
endpackage



module top ();
  import flash_ctrl_reg_pkg::*;

  flash_ctrl_reg2hw_mp_region_cfg_mreg_t [MpRegions:0] region_cfgs;

endmodule  
