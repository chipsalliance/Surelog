package config_pkg;

  typedef struct packed {
    bit                          RVC;
    logic [15:0][63:0]           PMPCfgRstVal;
  } cva6_user_cfg_t;

  
  typedef struct packed {
    int unsigned FETCH_WIDTH;
    int unsigned INSTR_PER_FETCH;
    logic [15:0][63:0]           PMPCfgRstVal;
  } cva6_cfg_t;

  /// Empty configuration to sanity check proper parameter passing. Whenever
  /// you develop a module that resides within the core, assign this constant.
  localparam cva6_cfg_t cva6_cfg_empty = '0;


endpackage

package cva6_config_pkg;

  localparam CVA6ConfigCExtEn = 1;
  
  localparam config_pkg::cva6_user_cfg_t cva6_cfg = '{
      RVC: bit'(CVA6ConfigCExtEn),
      PMPCfgRstVal: {16{64'h0}}
  };


endpackage



package build_config_pkg;

  function automatic config_pkg::cva6_cfg_t build_config_func(config_pkg::cva6_user_cfg_t CVA6Cfg);
  
    config_pkg::cva6_cfg_t cfg;
    cfg.PMPCfgRstVal = CVA6Cfg.PMPCfgRstVal;
    cfg.FETCH_WIDTH = 32;
    cfg.INSTR_PER_FETCH = CVA6Cfg.RVC == 1'b1 ? (cfg.FETCH_WIDTH / 16) : 1;
    
    return cfg;
  endfunction

  

  /*
  function automatic config_pkg::cva6_cfg_t build_config_func(config_pkg::cva6_user_cfg_t CVA6Cfg);
    config_pkg::cva6_cfg_t cfg;
    cfg.INSTR_PER_FETCH = CVA6Cfg.RVC == 1'b1;
    return cfg;
  endfunction
*/

  //localparam config_pkg::cva6_cfg_t DEBUG4 = build_config_func(cva6_config_pkg::cva6_cfg);
  //localparam DEBUG5 = DEBUG4.INSTR_PER_FETCH;
endpackage



module top();
 //parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty;

  parameter config_pkg::cva6_cfg_t CVA6Cfg = build_config_pkg::build_config_func(
        cva6_config_pkg::cva6_cfg);


  //parameter DEBUG5 = CVA6Cfg.INSTR_PER_FETCH;


  //localparam DEBUG4 = build_config_pkg::build_config_func(cva6_config_pkg::cva6_cfg);
  //localparam DEBUG5 = DEBUG4.INSTR_PER_FETCH;

  
 popcount #(
        .INPUT_WIDTH(CVA6Cfg.INSTR_PER_FETCH)
    ) u1();

endmodule


module popcount #(parameter int unsigned INPUT_WIDTH = 2) ();

   //Recursive instantiation to build binary adder tree
   if (INPUT_WIDTH == 1) begin : single_node
    
   end else if (INPUT_WIDTH == 2) begin : leaf_node
     
   end else begin : non_leaf_node
     popcount #(.INPUT_WIDTH(PaddedWidth / 2))
         left_child();

     popcount #(.INPUT_WIDTH(PaddedWidth / 2))
         right_child();
   end

endmodule : popcount

