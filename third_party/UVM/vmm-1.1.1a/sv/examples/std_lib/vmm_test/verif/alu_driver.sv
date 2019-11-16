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


typedef class alu_driver;

class alu_driver_callbacks extends vmm_xactor_callbacks;
    virtual task pre_trans_t  (alu_driver driver,
                               alu_data tr,
                               bit drop);
    endtask

                               
   virtual task post_trans_t  (alu_driver driver,
                               alu_data tr
                               );
   endtask
endclass
    

class alu_driver extends vmm_xactor;
  alu_data_channel in_chan;

  virtual alu_if.drvprt iport;

  static integer TRANS_DONE;

  function new(string                inst,
               integer               stream_id,
               virtual alu_if.drvprt iport,
               alu_data_channel      in_chan = null);

      super.new("ALU Driver", inst, stream_id);
      if (in_chan == null)
         in_chan = new("ALU Driver input channel", inst);
      this.iport = iport;
      this.in_chan = in_chan;
      this.in_chan.set_consumer(this);

      this.TRANS_DONE = this.notify.configure(, vmm_notify::ON_OFF);
   endfunction


  protected virtual task main();
    fork
      super.main();
    join_none

    this.iport.cb.en <= 0;
    this.iport.cb.sel <= 0;
    this.iport.cb.a <= 4'bx;
    this.iport.cb.b <= 4'bx;

    forever begin
       alu_data tr;
       bit drop = 0;

       this.in_chan.get(tr);
       `vmm_callback(alu_driver_callbacks, pre_trans_t(this, tr, drop));

       if (drop) begin
          `vmm_debug(log, "Dropping transaction...");
          tr.display("alu_driver");
          continue;
       end

       tr.notify.indicate(vmm_data::STARTED); 

       this.iport.cb.sel <= tr.kind;
       this.iport.cb.en <= 1'b1;
       this.iport.cb.a <= tr.a;
       this.iport.cb.b <= tr.b;
       
       @(iport.cb);
       this.iport.cb.en <= 1'b0;       
       `vmm_callback(alu_driver_callbacks, post_trans_t(this, tr));

       this.notify.indicate(this.TRANS_DONE, tr);
       this.notify.indicate(vmm_data::ENDED);
       @(iport.cb);
    end
  endtask

endclass


