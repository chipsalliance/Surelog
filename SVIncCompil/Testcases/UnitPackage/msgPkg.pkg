//+++++++++++++++++++++++++++++++++++++++++++++++++
//   Package Declaration
//+++++++++++++++++++++++++++++++++++++++++++++++++
package msgPkg;
  integer  errCnt  = 0;
  integer  warnCnt = 0;
  bit      terminate_on_error = 0;
  string   msgName = "NULL";
  //=================================================
  // Initilizes the messaging
  //=================================================
  task initMsgPkg (string mName, bit term);
    terminate_on_error = term;
    msgName = mName;
  endtask
  //=================================================
  // Prints the INFO message
  //=================================================
  task  msg_info (string msg);
    $display ("@%0dns %s INFO : %s",$time,msgName,msg);
  endtask 
  //=================================================
  // Prints the warning message
  //=================================================
  task  msg_warn (string msg);
    $display ("@%0dns %s WARN : %s",$time,msgName,msg);
    warnCnt ++;
  endtask 
  //=================================================
  // Prints error message
  //=================================================
  task  msg_error (string msg);
    $display ("@%0dns %s ERROR : %s",$time,msgName,msg);
    errCnt ++;
    if (terminate_on_error) $finish;
  endtask 
  //=================================================
  // Prints fatal message and terminates simulation
  //=================================================
  task  msg_fatal (string msg);
    $display ("@%0dns %s FATAL : %s",$time,msgName,msg);
    $finish;
  endtask 
  //=================================================
  // Returns the error count
  //=================================================
  function integer getErrCnt();
    getErrCnt = errCnt;
  endfunction
  //=================================================
  // Returns the warning count
  //=================================================
  function integer getWarnCnt();
    getWarnCnt = warnCnt;
  endfunction

endpackage
