


//module foo(input logic [31:0] data);

//endmodule



module dut();

logic [31:0] data;

parameter logic [31:0] data = '{ default: 1 };

assign data = '{ default: 1 };

//foo f(.data('{ default: 1 }));


endmodule
