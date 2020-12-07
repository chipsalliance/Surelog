

class param_types_as_class_item;
  parameter type AT;
  typedef logic BrickType;
  parameter type BT = BrickType;
  parameter type CT1 = Ctype1, CT2 = Ctype2;
  localparam type GT = mypkg::GlueType, GT2;
  localparam type HT1, HT2 = mypkg::ModuleType#(N+M);
endclass


