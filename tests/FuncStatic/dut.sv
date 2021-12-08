module automatic test();

function static integer accumulate1(input integer value);
  static int acc = 1;
  acc = acc + value;
  return acc;
endfunction

function integer accumulate2(input integer value);
  int acc = 1;
  acc = acc + value;
  return acc;
endfunction

localparam value1 = accumulate1(2);
localparam value2 = accumulate1(3);
localparam value3 = accumulate2(2);
localparam value4 = accumulate2(3);

endmodule
