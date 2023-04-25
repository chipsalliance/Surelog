
package test_package;

  typedef enum logic {
    On  = 1,
    Off = 0
  } lc_tx_t;

  function automatic logic test_true(lc_tx_t val);
    return On == val;
  endfunction : test_true

endpackage


module top(input logic i, output logic o);
  assign o = test_package::test_true(i);
endmodule

