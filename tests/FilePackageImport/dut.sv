
package pkg_b;
typedef logic [1:0] DCacheWayPath;

endpackage : pkg_b

import pkg_b::*;

function automatic int
TreeLRU_CalcWriteEnable(logic weIn, DCacheWayPath way);
    return we;
endfunction