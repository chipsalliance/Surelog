/*
:name: string-word-assignment
:description: String assignment tests
:tags: 5.9
*/
module top();
  bit [8 * 3 - 1 : 0] a = "hi0";
  // Note as of January 2020 several commercial simulators do not support unpacked byte
  // assignment from strings:
  byte      b[3 : 0] = "hi2";

endmodule
