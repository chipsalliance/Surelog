module ibex_csr #(
    parameter bit [1:0] ResetValue = '0) ();
   
endmodule;

module top();
 

  typedef struct packed {
    logic mie;
    logic mpie;
  } status_t;

  localparam status_t MSTATUS_RST_VAL = '{mpie:  1'b1,
                                          mie: 1'b0};
  ibex_csr #(
    .ResetValue ({MSTATUS_RST_VAL})
  ) u_mstatus_csr();
endmodule

