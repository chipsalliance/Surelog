
import uvm_pkg::* ;
`include "uvm_macros.svh"

`uvm_analysis_imp_decl(_too_pkt)

`uvm_analysis_imp_decl(_rcvd_pkt)

`uvm_analysis_imp_decl(_sent_pkt)



package uvm_pkg;

class uvm_component;
endclass


endpackage



module uvm_pkg();

typedef enum {UNICAST=11,MULTICAST,BROADCAST} pkt_type;

class uvm_component #(type T1=int, type T2=T1);
 pkt_type typen;
 T1 e;
  T2 t;

   uvm_analysis_imp_rcvd_pkt #(Packet,Scoreboard) Rcvr2Sb_port;
    uvm_analysis_imp_sent_pkt #(Packet,Scoreboard) Drvr2Sb_port;

endclass

endmodule


package all_c;
  class E;
  endclass

 class D extends E;
 endclass


class uvm_blocking_get_export #(type T=int)
  extends uvm_port_base #(uvm_tlm_if_base #(T,T));
endclass 

class uvm_component;
endclass


virtual class uvm_port_base #(type IF=uvm_void) extends IF;
endclass   


endpackage



module top ();

import all_c::*;

   class C;
   endclass

   class A extends C;  
   endclass

   class B extends D;  
    A a;
   endclass

endmodule



class c3;
  c1 cc;
  function foo();
  endfunction
endclass

class c1;
  
  function int get_current_item(int i); 
    return i;
  endfunction
  
endclass

class c2 extends c3;

c1 d;

  function void x_b_transport (ref bits_t bits,
                               inout uint64 delay);
    T t;
    m_delay = new("x_b_transport_delay", 1.0e-12);
    t = new();
  endfunction

function void main(int ar);
  string q[$];
  q.push_back("report handler state dump \n\n");
  d.get_current_item(ar); 
  ar.get_current_item(ar); 
  foo();
  cc.get_current_item(ar); 
endfunction

endclass



class uvm_analysis_imp #(type T=int, type IMP=int);
  
  local IMP m_imp; 
  
  function void write (input T t);
    m_imp.write (t);
  endfunction
endclass



class c2 ;
  string m_stack[$];

function void main(int ar);
  string q[$];
  string blah;
  byte unsigned byte_data [];
  byte_data.reverse();
  byte_data.toto();
  q.push_back("report handler state dump \n\n");
  m_stack.push_back("report handler state dump \n\n");
  q.get_current_item(ar);
  blah.itoa(ar); 
  $foo();
endfunction

endclass


