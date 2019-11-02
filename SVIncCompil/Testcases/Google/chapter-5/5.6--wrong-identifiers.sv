/*
:name: wrong-identifiers
:description: Identifiers that should not be accepted
:should_fail: 1
:tags: 5.6
*/
module identifiers();
  reg $dollar;
  reg 0number;
endmodule
