package my_package1;

parameter  p1 = 1;
localparam p2 = 2;

typedef logic [1:0] word;

word v;

endpackage


module test();

import my_package1::*;

initial begin
  v = p1 + p2;
end

endmodule

