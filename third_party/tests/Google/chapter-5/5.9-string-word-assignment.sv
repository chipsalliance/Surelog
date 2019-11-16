/*
:name: string-word-assignment
:description: String assignment tests
:should_fail: 0
:tags: 5.9
*/
module top();
  bit   a[8 * 3 : 0] = "hi0";
  byte      b[3 : 0] = "hi2";

endmodule
