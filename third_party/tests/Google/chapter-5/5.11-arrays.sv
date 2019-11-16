/*
:name: arrays
:description: Basic arrays test
:should_fail: 0
:tags: 5.11
*/
module top();
  int n[1:2][1:3] = '{'{0,1,2},'{3{4}}};
endmodule
