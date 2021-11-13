package foo_pkg;
  parameter int VALUE_TEMP = '{default: 1};
endpackage

module bottom ();
  parameter int VALUE = 8;
endmodule

module lower ();
  import foo_pkg::*;
  parameter int VALUE = VALUE_TEMP + 2;
  bottom #(
    .VALUE(VALUE)
  ) bottom_u();
endmodule

module upper ();
  parameter int VALUE = 7;
  lower lower_u ();
endmodule

module top ();
  parameter int VALUE = 5;
  upper upper_u() ;
endmodule
