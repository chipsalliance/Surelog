// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    All Rights Reserved Worldwide
// 
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
// 
//        http://www.apache.org/licenses/LICENSE-2.0
// 
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
// 

//
// Description : Scoreboard for Memory Design
//

class dut_sb;

  vmm_log log;           // For log messages
  vmm_notify notify;

  int max_trans_cnt;     // Max # of transactions
  local int match;       // Number of good matches

  local fifo_trans from_master_q[$] ;  // queue of data from the master

  integer DONE;                       // DONE notification
    
  extern function new(int max_trans_cnt);

  extern task cleanup();

  extern function void from_master(fifo_trans tr);
  extern function void from_monitor(fifo_trans mon_tr);
endclass 

//-----------------------------------------------------------------------------
// new() - Constructor
//-----------------------------------------------------------------------------

function dut_sb::new(int max_trans_cnt);
  // Save the arguments into local data members
  this.log = new("Scoreboard", "Scoreboard");
  this.max_trans_cnt = max_trans_cnt;
  match = 0;   
  // Configure DONE notification to be ON/OFF
  this.notify = new(this.log);
  DONE = notify.configure(-1, vmm_notify::ON_OFF); 

endfunction: new

//-----------------------------------------------------------------------------
// from_master() - Entry point from master callback integration object
//-----------------------------------------------------------------------------

function void dut_sb::from_master(fifo_trans tr) ; 
  from_master_q.push_back(tr) ; 
endfunction: from_master

//-----------------------------------------------------------------------------
// from_monitor() - Entry point from monitor callback integration object
//                  and main comparions function
//-----------------------------------------------------------------------------

function void dut_sb::from_monitor(fifo_trans mon_tr); 
   fifo_trans mas_tr;

   // Since this device operates as a transfer function, the self-checking 
   // mechanism is quite simple. The scoreboard first waits for a
   // transaction to be generated then waits for the monitor to notify that 
   // this transaction occurred.  In order to determine the transaction 
   // correctness the following rules are applied:
   //   - Each generated WRITE transactions are stored to a register file 
   //    (which acts as a reference model in this case).
   //   - Each generated READ transactions get their data field filled from 
   //     the register file (so to provide an expected result).
   //   - each transactions is then compared on a first-come first-serve basis.
   `vmm_debug(this.log, mon_tr.psdisplay("Observed: "));

   if (this.from_master_q.size() == 0) begin
      `vmm_error(log, "Unexpected transaction");
      return;
   end
   mas_tr = from_master_q.pop_front();
   `vmm_debug(this.log, mas_tr.psdisplay("Expected: "));

    // Perform the comparison of master vs mon vs memory
   begin
      string diff;
      if (!mon_tr.compare(mas_tr, diff)) begin
         `vmm_error(log, $psprintf("Unexpected transaction: %s", diff));
      end else begin
         `vmm_note(log, mon_tr.psdisplay("Matched: "));
      end
   end
   match++;  

   // Determine if the end of test has been reached
   if (match >= max_trans_cnt) begin
      `vmm_note(this.log, $psprintf("Done scorboarding found %d matches", match));
      this.notify.indicate(this.DONE);
   end
endfunction: from_monitor


//-----------------------------------------------------------------------------
// cleanup() - RVM Cleanup Method
//-----------------------------------------------------------------------------

task dut_sb::cleanup();

endtask: cleanup

