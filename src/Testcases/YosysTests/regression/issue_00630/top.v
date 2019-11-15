module top(input in, output out);

function func;
  input arg;
  func = arg;
endfunction

assign out = func(in);

endmodule
