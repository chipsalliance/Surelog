package B;
  typedef logic C;
endpackage;

package D;
  import B::*;
endpackage;


package A;
  import D::*;
endpackage; // A
   
