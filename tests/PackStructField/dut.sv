
package my_package;

  typedef struct packed {
    logic a;
    logic b;
  } my_struct;

  parameter my_package::my_struct my_parameter = '{
    a: 1'b1,
    b: 1'b0
  };

endpackage : my_package

module my_module (
    output my_package::my_struct x,
    output my_package::my_struct y
);

assign x = my_package::my_parameter.a;
assign y = my_package::my_parameter.b;

endmodule : my_module