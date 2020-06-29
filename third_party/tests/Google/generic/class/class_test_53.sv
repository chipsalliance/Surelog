/*
:name: class_test_53
:description: Test
:tags: 6.15 8.3
*/
class param_types_as_class_item;
  parameter type AT;
  parameter type BT = BrickType;
  parameter type CT1 = Ctype1, CT2 = Ctype2;
  localparam type GT = mypkg::GlueType, GT2;
  localparam type HT1, HT2 = mypkg::ModuleType#(N+M);
endclass