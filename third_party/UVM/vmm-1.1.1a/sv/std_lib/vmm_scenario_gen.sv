//
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    Copyright 2008-2009 Mentor Graphics Corporation
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

`ifdef VCS2006_06
   // Work-around for NYI feature in VCS2006.06
   // but IEEE 1800-2009 compliant
   `define vmm_delQ(_q) _q.delete()
`else
`ifdef INCA
   `define vmm_delQ(_q) _q.delete()
`else
   // Works in VCS2008.03 or later
   // IEEE 1800-2005 compliant
   `define vmm_delQ(_q) _q = '{}
`endif
`endif

`define vmm_scenario_(class_name)                class_name``_scenario
`define vmm_scenario_valid_(class_name)          class_name``_scenario_valid
`define vmm_inject_item_scenario_(class_name)    class_name``_inject_item_scenario
`define vmm_atomic_scenario_(class_name)         class_name``_atomic_scenario
`define vmm_scenario_election_(class_name)       class_name``_scenario_election
`define vmm_scenario_election_valid_(class_name) class_name``_scenario_election_valid
`define vmm_scenario_gen_(class_name)            class_name``_scenario_gen
`define vmm_scenario_gen_callbacks_(class_name)  class_name``_scenario_gen_callbacks

`define vmm_scenario_gen(class_name, text) \
`vmm_scenario_gen_using(class_name, class_name``_channel, text)

`define vmm_scenario_gen_using(class_name, channel_name, text) \
 \
class `vmm_scenario_(class_name) extends `VMM_SCENARIO; \
 \
   static `VMM_LOG log; \
 \
   rand class_name items[]; \
        class_name using; \
 \
   local virtual function string this_class_name(); \
      return `"`vmm_scenario_(class_name)`"; \
   endfunction: this_class_name \
 \
   local virtual function vmm_log get_vmm_log(); \
      return this.log; \
   endfunction: get_vmm_log \
 \
   local virtual function string __default_name(); \
      return {"Undefined ", text, " Scenario"}; \
   endfunction: __default_name \
 \
   virtual function string psdisplay(string prefix = ""); \
      psdisplay = super.psdisplay(prefix); \
      `foreach (this.items,i) begin \
         string pfx; \
         if (this.items[i] == null) continue; \
         $sformat(pfx, "%s  Item[%0d]: ", prefix, i); \
         psdisplay = {psdisplay, "\n", this.items[i].psdisplay(pfx)}; \
      end \
      if (this.using != null) begin \
         psdisplay = {psdisplay, "\n", this.using.psdisplay({prefix, "  Using: "})}; \
      end \
      return psdisplay; \
   endfunction: psdisplay \
 \
   constraint `vmm_scenario_valid_(class_name) { \
      items.size() == length; \
 \
`ifdef VMM_SOLVE_BEFORE_SIZE \
      solve length before items.size `VMM_SOLVE_BEFORE_OPT; \
`endif \
   } \
 \
   function new(`VMM_SCENARIO_NEW_ARGS); \
      super.new(null `VMM_SCENARIO_NEW_CALL ); \
      using = null; \
   endfunction: new \
 \
   virtual function vmm_data copy(vmm_data to = null); \
      `vmm_scenario_(class_name) cpy; \
 \
      if (to == null) cpy = new(); \
      else if (!$cast(cpy, to)) begin \
         `vmm_fatal(this.log, {"Cannot copy to non-", `VMM_MACRO_TO_STRING(`vmm_scenario_(class_name)), " instance"}); \
         return null; \
      end \
 \
      void'(super.copy(cpy)); \
      cpy.items = new [this.items.size()]; \
      `foreach (this.items,i) begin \
         if (this.items[i] == null) cpy.items[i] = null; \
         else $cast(cpy.items[i], this.items[i].copy()); \
      end \
      if (this.using == null) cpy.using = null; \
      else $cast(cpy.using, this.using.copy()); \
 \
      return cpy; \
   endfunction: copy \
 \
   function void allocate_scenario(class_name using = null); \
      this.items = new [this.get_max_length()]; \
      `foreach (this.items,i) begin \
         if (using == null) this.items[i] = new; \
         else $cast(this.items[i], using.copy()); \
         `VMM_OBJECT_SET_PARENT(this.items[i], this) \
 \
         this.items[i].stream_id   = this.stream_id; \
         this.items[i].scenario_id = this.scenario_id; \
         this.items[i].data_id     = i; \
      end \
   endfunction: allocate_scenario \
 \
   function void fill_scenario(class_name using = null); \
      int i; \
 \
      if (this.items.size() < this.get_max_length()) begin \
         this.items = new [this.get_max_length()] (this.items); \
      end \
      `foreach (this.items,i) begin \
         if (this.items[i] != null) continue; \
 \
         if (using == null) this.items[i] = new; \
         else $cast(this.items[i], using.copy()); \
         `VMM_OBJECT_SET_PARENT(this.items[i], this) \
 \
         this.items[i].stream_id   = this.stream_id; \
         this.items[i].scenario_id = this.scenario_id; \
         this.items[i].data_id     = i; \
      end \
   endfunction: fill_scenario \
 \
   function void pre_randomize(); \
      this.fill_scenario(this.using); \
   endfunction: pre_randomize \
 \
   virtual task apply(channel_name     channel, \
                      ref int unsigned n_insts); \
      int i; \
 \
      for (i = 0; i < this.length; i++) begin \
         class_name item; \
         $cast(item, this.items[i].copy()); \
`ifndef VMM_GRAB_DISABLED \
         channel.put(item,,this); \
`else \
         channel.put(item); \
`endif \
      end \
 \
      n_insts = this.length; \
   endtask: apply \
endclass: `vmm_scenario_(class_name) \
 \
 \
class `vmm_inject_item_scenario_(class_name) extends `vmm_scenario_(class_name); \
 \
   function new(class_name obj `VMM_DATA_NEW_ARGS); \
      super.new(`VMM_DATA_NEW_CALL); \
 \
      this.items    = new [1]; \
      this.items[0] = obj; \
      this.length   = 1; \
      this.repeated = 0; \
      void'(this.define_scenario("Directed 'inject_obj()' transaction", 1)); \
   endfunction: new \
 \
   virtual task apply(channel_name     channel, \
                      ref int unsigned n_insts); \
`ifndef VMM_GRAB_DISABLED \
      channel.put(this.items[0],,this); \
`else \
      channel.put(this.items[0]); \
`endif \
      n_insts = 1; \
   endtask: apply \
 \
endclass: `vmm_inject_item_scenario_(class_name) \
 \
 \
class `vmm_atomic_scenario_(class_name) extends `vmm_scenario_(class_name); \
 \
   int unsigned ATOMIC; \
 \
   constraint atomic_scenario { \
      if (scenario_kind == ATOMIC) { \
         length == 1; \
         repeated == 0; \
      } \
   } \
 \
   function new(`VMM_DATA_NEW_ARGS); \
      super.new(`VMM_DATA_NEW_CALL); \
 \
      this.ATOMIC = this.define_scenario("Atomic", 1); \
 \
      this.scenario_kind   = this.ATOMIC; \
      this.length = 1; \
   endfunction: new \
 \
   virtual function string psdisplay(string prefix = ""); \
      psdisplay = super.psdisplay(prefix); \
   endfunction:psdisplay \
 \
   function void pre_randomize(); \
      super.pre_randomize(); \
   endfunction \
 \
   virtual task apply(channel_name     channel, \
                      ref int unsigned n_insts); \
      super.apply(channel, n_insts); \
   endtask: apply \
 \
endclass: `vmm_atomic_scenario_(class_name) \
 \
 \
class `vmm_scenario_election_(class_name); \
   int stream_id; \
   int scenario_id; \
   int unsigned n_scenarios; \
   int unsigned last_selected[$]; \
   int unsigned next_in_set; \
 \
   `vmm_scenario_(class_name) scenario_set[$]; \
 \
   rand int select; \
 \
   constraint `vmm_scenario_election_valid_(class_name) { \
      select >= 0; \
      select < n_scenarios; \
   } \
 \
   constraint round_robin { \
      select == next_in_set; \
   } \
 \
endclass: `vmm_scenario_election_(class_name) \
 \
typedef class `vmm_scenario_gen_(class_name); \
 \
class `vmm_scenario_gen_callbacks_(class_name) extends vmm_xactor_callbacks; \
   virtual task pre_scenario_randomize(`vmm_scenario_gen_(class_name) gen, \
                                       ref `vmm_scenario_(class_name) scenario); \
   endtask \
 \
   virtual task post_scenario_gen(`vmm_scenario_gen_(class_name) gen, \
                                  `vmm_scenario_(class_name)     scenario, \
                                  ref bit                        dropped); \
   endtask \
endclass: `vmm_scenario_gen_callbacks_(class_name) \
 \
 \
class `vmm_scenario_gen_(class_name) extends `VMM_XACTOR; \
 \
   int unsigned stop_after_n_insts; \
   int unsigned stop_after_n_scenarios; \
 \
   typedef enum int {GENERATED, \
                     DONE} symbols_e; \
 \
   `vmm_scenario_election_(class_name) select_scenario; \
 \
   `vmm_scenario_(class_name) scenario_set[$]; \
   protected `vmm_scenario_(class_name) scenario_registry[string]; \
 \
   channel_name out_chan; \
 \
   protected int scenario_count; \
   protected int inst_count; \
 \
   virtual function string psdisplay(string prefix = ""); \
      psdisplay = super.psdisplay(prefix); \
      $sformat(psdisplay, "%s [stops after #insts %0d>%0d or #scenarios %0d>%0d]", \
               psdisplay, this.inst_count, this.stop_after_n_insts, \
               this.scenario_count, this.stop_after_n_scenarios); \
      $sformat(psdisplay, "%s\n%sOutChan: %s(%s) [level=%0d of %0d]", \
               psdisplay, prefix, this.out_chan.log.get_name(), \
               this.out_chan.log.get_instance(), this.out_chan.level(), \
               this.out_chan.full_level()); \
      `foreach_aa (this.scenario_registry,string,name) begin \
         psdisplay = {psdisplay, "\n", \
                      this.scenario_registry[name].psdisplay(prefix)}; \
      end \
      `foreach_aa_end (this.scenario_registry,name) \
      return psdisplay; \
   endfunction: psdisplay \
 \
   function new(string       inst, \
                int          stream_id = -1, \
                channel_name out_chan  = null \
                `VMM_XACTOR_NEW_ARGS); \
      super.new({text, " Scenario Generator"}, inst, stream_id \
                `VMM_XACTOR_NEW_CALL); \
 \
      if (out_chan == null) begin \
         out_chan = new({text, " Scenario Generator output channel"}, \
                        inst); \
         `VMM_OBJECT_SET_PARENT(out_chan, this) \
      end \
      this.out_chan = out_chan; \
      this.out_chan.set_producer(this); \
      this.log.is_above(this.out_chan.log); \
 \
      this.scenario_count = 0; \
      this.inst_count = 0; \
      this.stop_after_n_insts     = 0; \
      this.stop_after_n_scenarios = 0; \
 \
      this.select_scenario = new; \
      begin \
         `vmm_atomic_scenario_(class_name) sc = new; \
         `VMM_OBJECT_SET_PARENT(sc, this) \
         this.register_scenario("Atomic", sc); \
      end \
 \
      void'(this.notify.configure(GENERATED)); \
      void'(this.notify.configure(DONE, vmm_notify::ON_OFF)); \
   endfunction: new \
 \
   virtual function void register_scenario(string name, \
                                           `vmm_scenario_(class_name) scenario); \
      if(name == "") begin \
         `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name)); \
         return; \
      end \
\
      if(this.scenario_registry.exists(name)) begin \
         `vmm_error(this.log, `vmm_sformatf("%s already has an entry in the scenario registry", name)); \
         return; \
      end \
\
      if(scenario == null) begin \
         `vmm_error(this.log, `vmm_sformatf("scenario passed for %s is a null value", name)); \
         return; \
      end \
\
      this.scenario_registry[name] = scenario; \
\
      `foreach(this.scenario_set,i) begin \
         if(this.scenario_set[i] == scenario) \
            return; \
      end \
      this.scenario_set.push_back(scenario); \
   endfunction: register_scenario \
\
   virtual function bit scenario_exists(string name); \
        if(name == "") begin \
            `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name)); \
            return 0; \
        end \
\
        if(this.scenario_registry.exists(name)) \
            scenario_exists = 1; \
        else \
            scenario_exists = 0; \
    endfunction: scenario_exists \
\
   virtual function void replace_scenario(string name, \
                                           `vmm_scenario_(class_name) scenario); \
      if(name == "") begin \
         `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name)); \
         return; \
      end \
\
      if(scenario == null) begin \
         `vmm_error(this.log, `vmm_sformatf("scenario passed for %s is a null value", name)); \
         return; \
      end \
\
      if(!this.scenario_registry.exists(name)) begin \
         `vmm_error(this.log, `vmm_sformatf("cannot replace a unregistered %s entry [use register_scenario]", name)); \
         return ; \
      end \
\
      `foreach(this.scenario_set,i) begin \
         if(this.scenario_set[i] == this.scenario_registry[name]) begin \
            this.scenario_set.delete(i); \
            break; \
         end \
      end \
      this.scenario_registry[name] = scenario; \
      `foreach(this.scenario_set,i) begin \
          if(this.scenario_set[i] == scenario) \
              return; \
      end \
      this.scenario_set.push_back(scenario); \
   endfunction: replace_scenario \
\
   virtual function void get_all_scenario_names(ref string name[$]); \
      string s; \
\
      if(this.scenario_registry.first(s)) begin \
         do begin \
            name.push_back(s); \
         end while(this.scenario_registry.next(s)); \
      end \
      if(name.size() == 0) begin \
         `vmm_warning(this.log, "There are no entries in the scenario generator registry"); \
      end \
   endfunction: get_all_scenario_names \
\
   virtual function void get_names_by_scenario(`vmm_scenario_(class_name) scenario, \
                                               ref string name[$]); \
      string s; \
\
      if(scenario == null) begin \
         `vmm_error(this.log, `vmm_sformatf("scenario is a null value")); \
         return; \
      end \
\
      if(this.scenario_registry.first(s)) begin \
         do begin \
            if(this.scenario_registry[s] == scenario) \
               name.push_back(s); \
         end while(this.scenario_registry.next(s)); \
      end \
      if(name.size() == 0) begin \
         `vmm_warning(this.log, "There are no entries in the scenario registry"); \
      end \
   endfunction: get_names_by_scenario \
\
   virtual function string get_scenario_name(`vmm_scenario_(class_name) scenario); \
        string s[$]; \
\
        if(scenario == null) begin \
            `vmm_error(this.log, `vmm_sformatf("scenario is a null value")); \
            return ""; \
        end \
\
        this.get_names_by_scenario(scenario, s); \
\
        if(s.size()) \
            get_scenario_name = s[0]; \
        else \
            get_scenario_name = ""; \
   endfunction: get_scenario_name \
\
   virtual function int get_scenario_index(`vmm_scenario_(class_name) scenario); \
       get_scenario_index = -1; \
       `foreach(this.scenario_set,i) begin \
          if(this.scenario_set[i] == scenario) begin \
             return i; \
          end \
       end \
       if(get_scenario_index == -1) begin \
          `vmm_warning(this.log, `vmm_sformatf("Cannot find the index for the scenario")); \
       end \
   endfunction: get_scenario_index \
\
   virtual function bit unregister_scenario(`vmm_scenario_(class_name) scenario); \
      string s; \
      unregister_scenario=0; \
\
      if(scenario == null) begin \
         `vmm_error(this.log, `vmm_sformatf("scenario is a null value")); \
         return 0; \
      end \
      if(this.scenario_registry.first(s)) begin \
         do begin \
            if(this.scenario_registry[s] == scenario) begin \
               this.scenario_registry.delete(s); \
               unregister_scenario=1; \
            end \
         end while(this.scenario_registry.next(s)); \
      end \
      if(unregister_scenario==0) begin \
         `vmm_warning(this.log, "There are no entries in the scenario registry"); \
      end \
      if(unregister_scenario) begin \
         `foreach(this.scenario_set,i) begin \
            if(this.scenario_set[i] == scenario) begin \
               this.scenario_set.delete(i); \
               break; \
            end \
         end \
      end \
   endfunction: unregister_scenario \
\
   virtual function `vmm_scenario_(class_name) unregister_scenario_by_name(string name); \
      if(name == "") begin \
         `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name)); \
         return null; \
      end \
      if(!this.scenario_registry.exists(name)) begin \
         `vmm_warning(this.log, `vmm_sformatf("There is no entry for %s in the scenario registry", name)); \
         return null; \
      end \
      else begin \
         unregister_scenario_by_name = this.scenario_registry[name]; \
         `foreach(this.scenario_set,i) begin \
            if(this.scenario_set[i] == this.scenario_registry[name]) begin \
               this.scenario_set.delete(i); \
               break; \
            end \
         end \
         this.scenario_registry.delete(name); \
      end \
   endfunction: unregister_scenario_by_name \
\
   virtual function `vmm_scenario_(class_name) get_scenario(string name); \
      if(name == "") begin \
         `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name)); \
         return null; \
      end \
      if(!this.scenario_registry.exists(name)) begin \
         `vmm_error(this.log, `vmm_sformatf("%s does not have an entry in the scenario registry", name)); \
         return null; \
      end \
\
      get_scenario = this.scenario_registry[name]; \
      if(get_scenario == null) \
         `vmm_warning(this.log, `vmm_sformatf("%s has a null scenario associated with it in the scenario registry", name)); \
\
   endfunction: get_scenario \
 \
   function int unsigned get_n_insts(); \
      get_n_insts = this.inst_count; \
   endfunction: get_n_insts \
 \
   function int unsigned get_n_scenarios(); \
      get_n_scenarios = this.scenario_count; \
   endfunction: get_n_scenarios \
 \
   virtual task inject_obj(class_name obj); \
      `vmm_inject_item_scenario_(class_name) scenario = new(obj); \
      this.inject(scenario); \
   endtask: inject_obj \
 \
   local semaphore sem = new(1); \
 \
   virtual task inject(`vmm_scenario_(class_name) scenario); \
      bit drop = 0; \
 \
       sem.get(); \
 \
      // we're done, so abort injection \
      if (this.stop_after_n_insts > 0 && \
          this.inst_count >= this.stop_after_n_insts) begin \
          return; // without giving back the semaphore \
      end \
 \
      // we're done, so abort injection \
      if (this.stop_after_n_scenarios > 0 && \
          this.scenario_count >= this.stop_after_n_scenarios) begin \
          return; // without giving back the semaphore \
      end \
 \
      scenario.stream_id   = this.stream_id; \
      scenario.scenario_id = this.scenario_count; \
      `foreach (scenario.items,i) begin \
         scenario.items[i].stream_id   = scenario.stream_id; \
         scenario.items[i].scenario_id = scenario.scenario_id; \
         scenario.items[i].data_id     = i; \
      end \
 \
      `vmm_callback(`vmm_scenario_gen_callbacks_(class_name), \
                    post_scenario_gen(this, scenario, drop)); \
 \
      if (!drop) begin \
         this.scenario_count++; \
         this.notify.indicate(GENERATED, scenario); \
 \
         if (scenario.repeated > scenario.repeat_thresh) begin \
            `vmm_warning(this.log, `vmm_sformatf("A scenario will be repeated %0d times...", \
                                                 scenario.repeated)); \
         end \
         repeat (scenario.repeated + 1) begin \
            int unsigned n_insts = 0; \
            scenario.apply(this.out_chan, n_insts); \
            this.inst_count += n_insts; \
         end \
      end \
 \
      sem.put(); \
 \
   endtask: inject \
 \
   virtual function void reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST); \
      super.reset_xactor(rst_typ); \
      this.scenario_count = 0; \
      this.inst_count     = 0; \
      this.out_chan.flush(); \
      sem = new(1); \
      `vmm_delQ(this.select_scenario.last_selected); \
 \
      if (rst_typ >= FIRM_RST) begin \
         this.notify.reset( , vmm_notify::HARD); \
      end \
 \
      if (rst_typ >= HARD_RST) begin \
         `vmm_atomic_scenario_(class_name) sc = new; \
         `VMM_OBJECT_SET_PARENT(sc, this) \
 \
         this.stop_after_n_insts     = 0; \
         this.stop_after_n_scenarios = 0; \
         this.select_scenario = new; \
         this.scenario_set.push_back(sc); \
      end \
 \
   endfunction: reset_xactor \
 \
   virtual protected task main(); \
      `vmm_scenario_(class_name) the_scenario; \
 \
      fork \
         super.main(); \
      join_none \
 \
      if(this.scenario_set.size() == 0) \
          return; \
 \
      while ((this.stop_after_n_insts <= 0 \
              || this.inst_count < this.stop_after_n_insts) \
             && (this.stop_after_n_scenarios <= 0 \
                 || this.scenario_count < this.stop_after_n_scenarios)) begin \
 \
         this.wait_if_stopped(); \
 \
         this.select_scenario.stream_id    = this.stream_id; \
         this.select_scenario.scenario_id  = this.scenario_count; \
         this.select_scenario.n_scenarios  = this.scenario_set.size(); \
         this.select_scenario.scenario_set = this.scenario_set; \
         if (this.select_scenario.last_selected.size() == 0) \
            this.select_scenario.next_in_set = 0; \
         else \
            this.select_scenario.next_in_set = ((this.select_scenario.last_selected[$] + 1) % this.scenario_set.size()); \
 \
         if (!this.select_scenario.randomize()) begin \
            `vmm_fatal(this.log, "Cannot select scenario descriptor"); \
            continue; \
         end \
 \
         if (this.select_scenario.select < 0 || \
             this.select_scenario.select >= this.scenario_set.size()) begin \
            `vmm_fatal(this.log, `vmm_sformatf("Select scenario #%0d is not within available set (0-%0d)", \
                                               this.select_scenario.select, \
                                               this.scenario_set.size()-1)); \
            continue; \
         end \
 \
         this.select_scenario.last_selected.push_back(this.select_scenario.select); \
         while (this.select_scenario.last_selected.size() > 10) begin \
            void'(this.select_scenario.last_selected.pop_front()); \
         end \
 \
         the_scenario = this.scenario_set[this.select_scenario.select]; \
         if (the_scenario == null) begin \
            `vmm_fatal(this.log, `vmm_sformatf("Selected scenario #%0d does not exist", \
                                               this.select_scenario.select)); \
            continue; \
         end \
 \
         the_scenario.stream_id   = this.stream_id; \
         the_scenario.scenario_id = this.scenario_count; \
         `foreach (the_scenario.items,i) begin \
            if (the_scenario.items[i] == null) continue; \
 \
            the_scenario.items[i].stream_id   = the_scenario.stream_id; \
            the_scenario.items[i].scenario_id = the_scenario.scenario_id; \
            the_scenario.items[i].data_id     = i; \
         end \
 \
         `vmm_callback(`vmm_scenario_gen_callbacks_(class_name), \
                       pre_scenario_randomize(this, the_scenario)); \
         if (the_scenario == null) continue; \
 \
         if (!the_scenario.randomize()) begin \
            `vmm_fatal(this.log, $psprintf("Cannot randomize scenario descriptor #%0d", \
                                           this.select_scenario.select)); \
            continue; \
         end \
 \
         this.inject(the_scenario); \
      end \
 \
      this.notify.indicate(DONE); \
      this.notify.indicate(XACTOR_STOPPED); \
      this.notify.indicate(XACTOR_IDLE); \
      this.notify.reset(XACTOR_BUSY); \
      this.scenario_count++; \
   endtask: main \
  \
endclass: `vmm_scenario_gen_(class_name)
