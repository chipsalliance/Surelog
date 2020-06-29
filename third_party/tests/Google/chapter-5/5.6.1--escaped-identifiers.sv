/*
:name: escaped-identifiers
:description: Escaped identifiers that should be accepted
:tags: 5.6.1
*/
module identifiers();

  reg \busa+index ;
  reg \-clock ;
  reg \***error-condition*** ;
  reg \net1/\net2 ;
  reg \{a,b} ;
  reg \a*(b+c) ;

endmodule
