
package pkg;
class Configuration1;
endclass

typedef  enum {IDLE,WRITE,READ,DONE} fsm_t_pkg;

endpackage

class Configuration2;
endclass

module bottom ();
endmodule

module top ();
 import pkg::*; 
typedef  enum {IDLE,WRITE,READ,DONE} fsm_t;

fsm_t state;
fsm_t_pkg state2;

bottom bot();
 
Environment env;
Configuration1 cfg;
Configuration2 cfg;
endmodule

