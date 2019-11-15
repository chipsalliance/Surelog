/*
:name: class_test_64
:description: Test
:should_fail: 0
:tags: 6.15 8.3
*/
class pp_class;
  int num_packets;
`ifdef DEBUGGER
  string source_name;
  string dest_name;
`endif
  int router_size;
endclass