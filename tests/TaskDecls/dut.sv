package uvm_pkg;

task uvm_wait_for_nba_region;

  int nba;
  int next_nba;

  next_nba++;
  nba <= next_nba;
  @(nba);


endtask

endpackage // uvm_pkg
   
   
