/*
:name: debug-directives
:description: Debugging compiler directives
:tags: 5.6.4
*/

module directives();
  initial $display("At %s @ %d\n", `__FILE__, `__LINE__);
endmodule;
