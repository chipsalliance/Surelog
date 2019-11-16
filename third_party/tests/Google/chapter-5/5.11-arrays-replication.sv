/*
:name: arrays-replication
:description: Basic arrays test
:should_fail: 0
:tags: 5.11
*/
module top();
  int n[1:2][1:6] = '{2{'{3{4, 5}}}};
endmodule
