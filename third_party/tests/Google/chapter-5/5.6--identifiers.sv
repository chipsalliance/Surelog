/*
:name: identifiers
:description: Identifiers that should be accepted
:should_fail: 0
:tags: 5.6
*/
module identifiers();
  reg shiftreg_a;
  reg busa_index;
  reg error_condition;
  reg merge_ab;
  reg _bus3;
  reg n$657;

  /* Should also be case sensitive,
   * should not cause a conflict here
   */
  reg sensitive;
  reg Sensitive;
endmodule
