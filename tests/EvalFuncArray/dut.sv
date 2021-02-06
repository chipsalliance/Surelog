package earlgrey;

parameter int InfosPerBank    = max_info_pages('{
    10,
    1,
    14,
    18,
    12
  });
parameter int InfoTypes = 5;

   function automatic integer max_info_pages(int infos[InfoTypes]);
   
    int current_max = 0;
    for (int i = 0; i < InfoTypes; i++) begin
      if (infos[i] > current_max) begin
        current_max = infos[i];
      end
    end
    return current_max;
  endfunction // max_info_banks


endpackage


