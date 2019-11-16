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


typedef class vmm_xvc_event;
typedef class xvc_xactor;
typedef class vmm_xvc_scenario;
typedef class vmm_xvc_manager;

`ifdef VCS
(* vmm_private_class, _vcs_vmm_class = 1 *)
`endif
class vmm_xvc_event_all;
   string     idQ[$];
   int        ev_idQ[$];
   vmm_notify notifyQ[$]; //these handles are computed at run-time from idQ
 
   vmm_xvc_manager xvc_mgr;                     
   vmm_xvc_scenario sc;
   vmm_log log;
   local string map_string;
 
   function bit split(string     command,
                      string     splt,
                      ref string tok[$]);
   string pre;
   string post;
   
   //some basic checks on inputs
   if (command.len() == 0 || splt.len == 0) begin
`ifdef VCS2006_06
      // Work-around for NYI feature in VCS2006.06
      // but IEEE 1800-2009 compliant
      tok.delete();
`else
`ifdef INCA
      tok.delete();
`else
      // Works in VCS2008.03 or later
      // IEEE 1800-2005 compliant
      tok = '{};
`endif
`endif
      return 0;
   end

   post = command;
   forever begin
      if (`vmm_str_match(post, splt)) begin
         pre = `vmm_str_prematch(post);
         post = `vmm_str_postmatch(post);
         if (pre.len() != 0) begin
            // Only add the token if non-empty to strip leading blanks
            tok.push_back(pre);
         end
      end else begin
         //if no further matches, put in the last match if it's non-zero len
         if (post.len() > 0) begin
            tok.push_back(post);
         end
         break;
      end
   end
   split = 1;
endfunction: split

   //set the notifyQ[$] from the idQ[$] at run time
   task get_event_handles();
      //foreach id, if id does not contain "." i.,e not x.y
      //check local events first, ie., this.sc.events[id]
      //next  check global events ie., xvc_mgr.events[id]
      //  Ignore if it does not exist ? - rvm_error
      //if id is of the from sid.sev
      //  get handle from xvc_mgr.scenarios[sid].events[sev]
      //
      if (this.idQ.size == 0)
         return;
      `foreach (this.idQ,i) begin
         if (`vmm_str_match(this.idQ[i], "[.]")) begin
             string event_info[2];
             int ev_id;
             vmm_xvc_scenario scn;
             event_info[0] = `vmm_str_prematch(this.idQ[i]);
             event_info[1] = `vmm_str_postmatch(this.idQ[i]);

             //lookup scenario event_info[0]
             scn = this.xvc_mgr.lookup_scenario(event_info[0]);

             //Warn if scn is null, continue
             if (scn == null) begin
                `vmm_fatal(this.log,
                             $psprintf("Mapevent: Scenario %s does not exist",
                                       event_info[0])
                             );
                continue;
             end

             //Get a handle to the sid.sev event
             ev_id = event_info[1].atoi();
             if (!scn.events.exists(ev_id)) begin
                `vmm_fatal(this.log,
                             $psprintf("Mapevent: Scenario %s does not have any event %0d",
                                    event_info[0],
                                    ev_id
                                    )
                          );
                continue;
             end
             this.ev_idQ.push_back(ev_id);
             this.notifyQ.push_back(scn.notify);
         end else begin
             int ev_id;
             bit is_ev_found = 0;
             ev_id = this.idQ[i].atoi;

             //first check if the event exists in current-scenario
             if (this.sc != null) begin
                if (this.sc.events.exists(ev_id)) begin
                   this.ev_idQ.push_back(ev_id);
                   this.notifyQ.push_back(this.sc.notify);
                   is_ev_found = 1;
                end 
             //then check global events
             end 
             if ((!is_ev_found) && this.xvc_mgr.events.exists(ev_id)) begin
                this.ev_idQ.push_back(ev_id);
                this.notifyQ.push_back(this.xvc_mgr.notify);
                is_ev_found = 1;
             end 
             if (!is_ev_found) begin
                `vmm_fatal(this.log,
                             $psprintf("Mapevent: Event %0d does not exist in Scenario %s or in Global space",
                                    ev_id,
                                    sc.name
                                    )
                             );
                continue;
             end
         end
      end

   endtask: get_event_handles

   //wait for *all* id's to complete
   task wait_for();

      //wait for all idQ to be seen
      `foreach (this.ev_idQ,i) begin
         automatic int j = i;
         fork
            this.notifyQ[j].wait_for(this.ev_idQ[j]);
         join_none
      end
      wait fork;
   endtask: wait_for
  
   function new(string s, vmm_xvc_manager xvcm, vmm_xvc_scenario sc, vmm_log log) ;
      string s2[$];
      this.map_string = s;
      //split by "+" into string subarrays using split
      //  ignore white space in separator
      this.split(s,"[\s\t]*[+][\s\t]*",s2);
      foreach (s2[i]) begin
         this.idQ.push_back(s2[i]);
      end
      this.xvc_mgr = xvcm;
      this.sc      = sc;
      this.log     = log;
   endfunction: new

endclass: vmm_xvc_event_all

//xvc_event_any_all
//   this is a representation of a compound event
//   Two-dimensional queues are not allowed, hence the 
//   data structure chosen is a queue class containing
//   another queue class to represent 2-D queues. 
//   The form of the compound event is a {any of{all of ev_list}}
`ifdef VCS
(* vmm_private_class, _vcs_vmm_class = 1 *)
`endif
class vmm_xvc_event_any_all extends vmm_xvc_event;
   vmm_xvc_event_all idQ[$];
   local string map_string;

   virtual task init();
      `foreach (this.idQ,i) begin
          this.idQ[i].get_event_handles();
      end
   endtask: init
   
   virtual task wait_for();
      event local_done_ev;
      //wait for any of products to be seen.
      `foreach (this.idQ,i) begin
          automatic int j = i;
          fork
             begin
                this.idQ[j].wait_for();
                ->local_done_ev;
             end
          join_none
      end
      @(local_done_ev); 
      disable fork;
   endtask: wait_for

   //create a sum-of-products representation from the string
   //  String of type: a+b,c+d,e (where a,b,etc are [0-9.]*
   //  This will be split up into (a)+(b,c)+(d,e) as the
   //    "," (AND) has precedence over "+" (OR)
   //  The function of splitting is done in TCL, and 
   //    results read in this function.
   function new(int id, 
                string descr, 
                string map_str,
                bit is_global, 
                bit is_oneshot, 
                vmm_log log, 
                vmm_notify notify,
                vmm_xvc_scenario sc,
                vmm_xvc_manager xvcm);
         
      string s2[$];

      super.new(id,
                descr,
                is_global,
                is_oneshot,
                log,
                notify,
                sc,
                xvcm);
      this.map_string = map_str;

      //Create sub-events for each product in the Sum-of-products.
      //split by "," into string subarrays using split,
      //  ignore whitespace in separators
      begin
         vmm_xvc_event_all tmp = new("", null, null, null);
         tmp.split(map_str,"[\s\t]*,[\s\t]*",s2);
      end
      foreach (s2[i]) begin
         vmm_xvc_event_all xall;
         xall = new(s2[i], 
                    xvcm, 
                    sc,
                    log);
         this.idQ.push_back(xall);
      end

   endfunction: new

endclass: vmm_xvc_event_any_all

//local event attached to an XVC
`ifdef VCS
(* vmm_private_class, _vcs_vmm_class = 1 *)
`endif
class vmm_xvc_event_local;
  int id;
  xvc_xactor xvc;
   
  task wait_for() ;
     this.xvc.notify.wait_for(this.id);
`ifdef VMM_DETAILED_MSGS
     if (this.xvc.log.start_msg(vmm_log::INTERNAL_TYP , vmm_log::TRACE_SEV )) begin
        void'(this.xvc.log.text($psprintf("Seen event %0d in xvc [%s]%s",
                          this.id, 
                          this.xvc.get_name(), 
                          this.xvc.get_instance())));
        this.xvc.log.end_msg();
     end
`endif
  endtask: wait_for

  //create mapping to xvcs
  function new(xvc_xactor xvc, int id);
     this.xvc = xvc;
     this.id = id;
   
     // configure this event as a oneshot event
     //   if it is not already configured
     if (!this.xvc.notify.is_configured(this.id))
        void'(this.xvc.notify.configure(this.id));
  endfunction: new

endclass: vmm_xvc_event_local

`ifdef VCS
(* vmm_private_class, _vcs_vmm_class = 1 *)
`endif
class vmm_xvc_event;
   int id;
   bit is_global;  //1 if this is global
   bit is_oneshot; //1 if this is oneshot 
   string descr;
   vmm_log    log;
   vmm_notify notify;
   vmm_xvc_scenario sc;
   vmm_xvc_manager xvc_mgr;                     
   local event thread_done_ev;

   //Any run-time initializations to be done
   virtual task init();
   endtask: init

   virtual task wait_for();
   endtask: wait_for

   virtual task indicate();
       this.notify.indicate(this.id);
   endtask: indicate

   //start threads to raise notification when any of the sub-events happen
   virtual task start();
      fork
         begin
         fork
            begin
               while (1) begin
                  this.wait_for();
                  this.indicate();
                  if (this.is_oneshot)
                     break;
               end
            end
            begin
               @(this.thread_done_ev);
            end
         join_any
         disable fork;
         end
      join_none
   endtask: start

   //The actual termination functionality in the 
   //  derived classes will terminate based on this event
   virtual task kill();
      ->this.thread_done_ev;
   endtask: kill

   function new(int id, 
                string descr, 
                bit is_global, 
                bit is_oneshot, 
                vmm_log log, 
                vmm_notify notify,
                vmm_xvc_scenario sc,
                vmm_xvc_manager xvcm);
         
     this.id         = id;
     this.descr      = descr;
     this.is_global  = is_global;
     this.is_oneshot = is_oneshot;
     this.log        = log;
     this.notify     = notify;
     this.sc         = sc;
     this.xvc_mgr    = xvcm;

     //configure the notifier with this id, in case its not
     //  already configured
     if (!this.notify.is_configured(this.id))
        void'(this.notify.configure(this.id ));

   endfunction: new
endclass: vmm_xvc_event

`ifdef VCS
(* vmm_private_class, _vcs_vmm_class = 1 *)
`endif
class vmm_xvc_event_mapped extends vmm_xvc_event;
   vmm_xvc_event_local xvcQ[$];  

   virtual task wait_for();
      event any_xvc_done_ev;
      fork
         begin
            //finish when *any* of the xvc's terminate
            foreach (xvcQ[i]) begin
                automatic int j = i;
                fork 
                   begin
                      xvcQ[j].wait_for();
                      ->any_xvc_done_ev;
                   end
                join_none
            end
            @(any_xvc_done_ev);
            disable fork;
         end
      join
   endtask: wait_for

   function new(int id, 
                string descr, 
                bit is_global, 
                bit is_oneshot, 
                vmm_log log, 
                vmm_notify notify,
                vmm_xvc_scenario sc,
                vmm_xvc_manager xvcm);

      super.new(id, 
                descr, 
                is_global, 
                is_oneshot, 
                log, 
                notify,
                sc,
                xvcm);

   endfunction: new

endclass: vmm_xvc_event_mapped

