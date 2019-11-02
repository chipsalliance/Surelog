/*
When a dotted name is encountered at its point of appearance, the first name in the sequence is resolved as
though it were a simple identifier. The following are the possible results:

a) The name resolves to a data object or interface port. The dotted name shall be considered to be a
select of that data object or interface port.

b) The name resolves to a directly visible scope name. The dotted name shall be considered to be a
hierarchical name.

c) The name resolves to an imported scope name. The dotted name shall be resolved in the same
manner as a hierarchical name prefixed by the package name from which the name was imported.

d) The name is not found. The dotted name shall be considered to be a hierarchical name.

*/

module m;

import p::*;
import bug::*;

if (package_param) 
  begin: sB1
    initial
    begin: bblock
      s1.x = 1;   // dotted name 1
      s2.x = 1;   // dotted name 2
      f.x = 1;    // dotted name 3
      f2.x = 1;   // dotted name 4
    end

    int x;
    some_module sInst();

  end

endmodule