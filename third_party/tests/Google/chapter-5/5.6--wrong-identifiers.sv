/*
:name: wrong-identifiers
:description: Identifiers that should not be accepted
:should_fail_because: the first character of a simple identifier shall not be a digit or $
:tags: 5.6
*/
module identifiers();
  reg $dollar;
  reg 0number;
endmodule
