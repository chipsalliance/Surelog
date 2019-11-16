
package pkg;
class Configuration1;
endclass

typedef  enum {IDLE,WRITE,READ,DONE} fsm_t_pkg;

endpackage

class Configuration2;
endclass


module top ();
 import pkg::*; 
typedef  enum {IDLE,WRITE,READ,DONE} fsm_t;

fsm_t state;
fsm_t_pkg state2;

Environment env;
Configuration1 cfg;
Configuration2 cfg;
endmodule

