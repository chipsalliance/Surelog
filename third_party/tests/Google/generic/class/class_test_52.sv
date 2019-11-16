/*
:name: class_test_52
:description: Test
:should_fail: 0
:tags: 6.15 8.3
*/
class how_wide #(type DT=int) extends uvm_sequence_item;
  localparam Max_int = {$bits(DT) - 1{1'b1}};
  localparam Min_int = {$bits(int) - $bits(DT){1'b1}};
endclass