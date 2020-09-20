package p1;

class c1;
  
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
   
   p3::c33 inst1;
  

endclass

endpackage
