
package pack;

 typedef struct packed {
    logic      A;
    logic      B;
  } status_t;

endpackage


module top3(); 
import pack::*;
 typedef struct packed {
    logic      mie;
    logic      mpie;
    priv_lvl_e mpp;
    logic      mprv;
    logic      tw;
  } status_t;
 localparam status_t MSTATUS_RST_VAL = '{mie:  1'b0,
                                          mpie: 1'b1,
                                          mpp:  PRIV_LVL_U,
                                          mprv: 1'b0,
                                          tw:   1'b0};
endmodule

