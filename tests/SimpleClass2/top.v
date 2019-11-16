
class uvm_pool;
  function add();
  endfunction

endclass

package p1;

class c1;
  string toto;

  extern function new (string name, uvm_component parent);

  function foo(string name = "");
   
    endfunction 

endclass


typedef c1 c3;

endpackage

package p3;
class c33;
endclass
endpackage   
   
package p2;
   
import p1::*;

class c2 extends c3;
   typedef uvm_pool#(string, uvm_action) uvm_id_actions_array;   
    uvm_id_actions_array id_actions;
   p3::c33 inst1;
   
 function new(string name = "svaunit_sequencer");
    super.new(name);
    super.foo(name);
    this.id_actions.add(id, action);
    id_actions.addq(id, action);
    super.toto.len();
    this.super.toto.len1();
   endfunction
          

endclass

endpackage


