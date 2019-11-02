// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    Copyright 2009 Mentor Graphics Corporation
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

class trans_driver extends vmm_xactor;

  trans_channel chans[$];

  function new(string inst, trans_channel chans[]);
     super.new("driver", inst);
     `ifdef INCA
     for (int i=0; i<chans.size(); ++i) begin
        this.chans.push_back(chans[i]);
        this.chans[i].set_consumer(this);
     end
     `else
     this.chans = chans;
     `endif
     `foreach (this.chans,i) begin
        this.chans[i].set_consumer(this);
     end
  endfunction

  virtual protected task main();
     fork
       super.main();
     join_none

     `foreach (this.chans,i) begin
        start_drive(this.chans[i], i);
     end
  endtask

  virtual task start_drive(vmm_channel chan, int i);
     vmm_data tr;
     fork
        forever begin
           chan.activate(tr);
           void'(chan.start());

           `vmm_note(log, tr.psdisplay($psprintf("Chan #%0d - Executing..", i)));
           #5;
           void'(chan.complete());
           void'(chan.remove());
        end
     join_none
  endtask
endclass

