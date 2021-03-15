package flash_ctrl_pkg;
  parameter int InfoTypes       = 3; // How many types of info per bank
  parameter int InfoTypeSize [InfoTypes] = '{
    10,
    1,
    2
  };
  parameter int InfosPerBank    = 10;
endpackage   


module flash_ctrl_info_cfg import flash_ctrl_pkg::*; ();

  parameter int InfoSel = 2;

  for(genvar i = 0; i < InfosPerBank; i++) begin : gen_info_priv


    if (i > InfoTypeSize[InfoSel]) begin : gen_invalid_region
      assign cfgs_o[i] = '0;
    end
  end
	    
endmodule // top
