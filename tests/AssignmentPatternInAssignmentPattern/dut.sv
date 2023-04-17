package ctrl_pkg;
  parameter int RegNumBanks = 2;
  parameter int RegPagesPerBank = 64;
endpackage

package pkg;
  parameter int unsigned NumBanks        = ctrl_pkg::RegNumBanks;
  parameter int unsigned PagesPerBank    = ctrl_pkg::RegPagesPerBank;
  parameter int HwDataRules = 2;
  parameter int MuBi4Width = 4;
  typedef enum logic [MuBi4Width-1:0] {
    MuBi4True = 4'h6,
    MuBi4False = 4'h9
  } mubi4_t;
  typedef enum logic [1:0] {
    PhaseSeed,
    PhaseRma,
    PhaseNone,
    PhaseInvalid
  } flash_lcmgr_phase_e;
  typedef struct packed {
    mubi4_t en;
  } mp_region_cfg_t;
  typedef struct packed {
    flash_lcmgr_phase_e   phase;
    mp_region_cfg_t cfg;
  } data_region_attr_t;
  parameter data_region_attr_t HwDataAttr = '{
       phase: PhaseSeed,
       cfg:   '{ en:          MuBi4True }
  };

endpackage

module foo
import pkg::*;
(
  input data_region_attr_t DATA_REG);
endmodule
module top();
import pkg::*;
foo f(.DATA_REG(HwDataAttr));

endmodule
