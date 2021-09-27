
module ibex_pmp #(
    // Granularity of NAPOT access,
    // 0 = No restriction, 1 = 8 byte, 2 = 16 byte, 3 = 32 byte, etc.
    parameter int unsigned PMPGranularity = 0,
    // Number of access channels (e.g. i-side + d-side)
    parameter int unsigned PMPNumChan     = 2,
    // Number of implemented regions
    parameter int unsigned PMPNumRegions  = 4
) (
   

);

  
  // ---------------
  // Access checking
  // ---------------

  for (genvar r = 0; r < PMPNumRegions; r++) begin : g_addr_exp
    
    // Address mask for NA matching
    for (genvar b = PMPGranularity+2; b < 34; b++) begin : g_bitmask
      if (b == PMPGranularity+2) begin : g_bit0
        
      end else begin : g_others
       
      end
    end
  end



endmodule
