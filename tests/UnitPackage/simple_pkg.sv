
//=================================================
// Import the Packages
//=================================================
import msgPkg::*;
import definesPkg::bool;

//+++++++++++++++++++++++++++++++++++++++++++++++++
// DUT Using the package
//+++++++++++++++++++++++++++++++++++++++++++++++++
module simple_package();

bool   value = definesPkg::FALSE;

if (SIZE > 1) begin : inst
   M1 u1();
  end

initial begin
  msgPkg::initMsgPkg("PACKAGES",0);
  msgPkg::msg_info("Testing Packages");
  #10 msgPkg::msg_warn("Testing Packages");
  #10 msgPkg::msg_error("Testing Packages");
  msgPkg::msg_info($psprintf("Warning Count %0d, Error Count %0d",
   msgPkg::getWarnCnt(), msgPkg::getErrCnt()));
  if (value != definesPkg::TRUE)  
    #10 msgPkg::msg_fatal("Value is FALSE");
end

endmodule
