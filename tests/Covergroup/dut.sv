covergroup cg ( ref int x , ref int y, input int c);
  coverpoint x;
  b: coverpoint y; 
  cx: coverpoint x;
  option.weight = c; // set weight of "cg" to value of formal "c"
  logic [7:0] d: coverpoint y[31:24]; // creates coverpoint "d" covering the
  // high order 8 bits of the formal "y"
  e: coverpoint x {
    option.weight = 2; // set the weight of coverpoint "e"
  }

  cross x, y {
    option.weight = c;
  }
endgroup


covergroup g4;
  coverpoint s0 iff(!reset);
endgroup
