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


`define vmm_atomic_gen_(class_name)           class_name``_atomic_gen
`define vmm_atomic_gen_callbacks_(class_name) class_name``_atomic_gen_callbacks


`define vmm_atomic_gen(class_name, text) \
`vmm_atomic_gen_using(class_name, class_name``_channel, text)

`define vmm_atomic_gen_using(class_name, channel_name, text) \
 \
typedef class `vmm_atomic_gen_(class_name); \
class `vmm_atomic_gen_callbacks_(class_name) extends vmm_xactor_callbacks; \
   virtual task post_inst_gen(`vmm_atomic_gen_(class_name) gen, \
                              class_name                   obj, \
                              ref bit                      drop); \
   endtask \
endclass \
 \
 \
class `vmm_atomic_gen_(class_name) extends `VMM_XACTOR; \
 \
   int unsigned stop_after_n_insts; \
 \
   typedef enum int {GENERATED, \
                     DONE} symbols_e; \
 \
 \
   class_name randomized_obj; \
 \
   channel_name out_chan; \
 \
   local int scenario_count; \
   local int obj_count; \
 \
   virtual function string psdisplay(string prefix = ""); \
      psdisplay = super.psdisplay(prefix); \
      $sformat(psdisplay, "%s [stops after #insts %0d>%0d]", \
               psdisplay, this.obj_count, this.stop_after_n_insts); \
      $sformat(psdisplay, "%s\n%sOutChan: %s(%s) [level=%0d of %0d]", \
               psdisplay, prefix, this.out_chan.log.get_name(), \
               this.out_chan.log.get_instance(), this.out_chan.level(), \
               this.out_chan.full_level()); \
      if (this.randomized_obj != null) begin \
         prefix = {prefix, "Factory: "}; \
         psdisplay = {psdisplay, "\n", \
                      this.randomized_obj.psdisplay(prefix)}; \
      end \
      return psdisplay; \
   endfunction: psdisplay \
 \
   function new(string       inst, \
                int          stream_id = -1, \
                channel_name out_chan  = null `VMM_XACTOR_NEW_ARGS); \
      super.new({text, " Atomic Generator"}, inst, stream_id `VMM_XACTOR_NEW_CALL); \
 \
      if (out_chan == null) begin \
         out_chan = new({text, " Atomic Generator output channel"}, \
                         inst); \
         `VMM_OBJECT_SET_PARENT(out_chan, this) \
      end \
      this.out_chan = out_chan; \
      this.out_chan.set_producer(this); \
      this.log.is_above(this.out_chan.log); \
 \
      this.scenario_count = 0; \
      this.obj_count = 0; \
      this.stop_after_n_insts = 0; \
 \
      void'(this.notify.configure(GENERATED, vmm_notify::ONE_SHOT)); \
      void'(this.notify.configure(DONE, vmm_notify::ON_OFF)); \
 \
      this.randomized_obj = new; \
      `VMM_OBJECT_SET_PARENT(this.randomized_obj, this) \
   endfunction: new \
 \
   local semaphore sem = new(1); \
 \
   virtual task inject(class_name obj, \
                       ref bit    dropped); \
      dropped = 0; \
 \
      sem.get(); \
 \
      if (this.stop_after_n_insts > 0 && \
          this.obj_count >= this.stop_after_n_insts) begin \
	  dropped=1; \
          sem.put(); \
          #0; // prevent 0-delay loops \
          return; \
      end \
 \
      `vmm_callback(`vmm_atomic_gen_callbacks_(class_name), \
                    post_inst_gen(this, obj, dropped)); \
 \
      if (!dropped) begin \
         this.obj_count++; \
         this.notify.indicate(GENERATED, obj); \
         this.out_chan.put(obj); \
      end \
 \
      sem.put(); \
      #0; \
 \
   endtask: inject \
 \
   virtual function void reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST); \
      super.reset_xactor(rst_typ); \
 \
      this.out_chan.flush(); \
      this.scenario_count = 0; \
      this.obj_count = 0; \
 \
      if (rst_typ >= FIRM_RST) begin \
         this.notify.reset( , vmm_notify::HARD); \
      end \
 \
      if (rst_typ >= HARD_RST) begin \
         this.stop_after_n_insts = 0; \
         this.randomized_obj     = new; \
      end \
   endfunction: reset_xactor \
 \
   virtual protected task main(); \
      bit dropped; \
 \
      fork \
         super.main(); \
      join_none \
 \
      while (this.stop_after_n_insts <= 0 || \
             this.obj_count < this.stop_after_n_insts) begin \
 \
         this.wait_if_stopped(); \
 \
         this.randomized_obj.stream_id   = this.stream_id; \
         this.randomized_obj.scenario_id = this.scenario_count; \
         this.randomized_obj.data_id     = this.obj_count; \
 \
         if (!this.randomized_obj.randomize()) begin \
            `vmm_fatal(this.log, "Cannot randomize atomic instance"); \
            continue; \
         end \
 \
         begin \
            class_name obj; \
 \
            $cast(obj, this.randomized_obj.copy()); \
            `VMM_OBJECT_SET_PARENT(obj, this) \
            this.inject(obj, dropped); \
         end \
      end \
 \
      this.notify.indicate(DONE); \
      this.notify.indicate(XACTOR_STOPPED); \
      this.notify.indicate(XACTOR_IDLE); \
      this.notify.reset(XACTOR_BUSY); \
      this.scenario_count++; \
   endtask: main \
 \
endclass
