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


`ifndef VMM_CONSENSUS__SV
`define VMM_CONSENSUS__SV


function vmm_consensus::new(string        name,
                            string        inst);
`ifdef VMM_CONSENSUS_BASE_NEW_CALL
   super.new(`VMM_CONSENSUS_BASE_NEW_CALL);
`endif

   this.log = new(name, inst);
   this.notify = new(log);
   void'(this.notify.configure(NEW_VOTE));

   this.n_dissenters = 0;
   this.n_forcing    = 0;
endfunction: new


function vmm_voter vmm_consensus::register_voter(string name);
   vmm_voter voter = new(name, this);

   // Voters object by default
   this.n_dissenters++;

   this.voters.push_back(voter);

   return voter;
endfunction: register_voter


function void vmm_consensus::unregister_voter(vmm_voter voter);
   `foreach (this.voters,i) begin
      if (this.voters[i] == voter) begin
         if (!voter.get_vote()) voter.consent("Dead voter consents by default");
         voter.kill_voter();
         this.voters.delete(i);
         return;
      end
   end
   `vmm_error(this.log, {voter.get_name(), " is not a registered voter"});
endfunction: unregister_voter


function void vmm_consensus::register_xactor(vmm_xactor xact);
   vmm_voter voter;
   if(xact == null) begin
     `vmm_error(this.log,"Trying to register null vmm_xactor reference");
     return;
   end
   voter = this.register_voter({"Transactor ", xact.get_name(),
                                          "(", xact.get_instance(), ")"});
   voter.xactor(xact);
endfunction: register_xactor


function void vmm_consensus::unregister_xactor(vmm_xactor xact);
   `foreach (this.voters,i) begin
      vmm_voter voter = this.voters[i];
      if (voter.get_xactor() == xact) begin
         if (!voter.get_vote()) voter.consent("Dead voter consents by default");
         voter.kill_voter();
         this.voters.delete(i);
         return;
      end
   end
   `vmm_error(this.log, {"Transactor ", xact.get_name(), "(",
                         xact.get_instance(), ") is not a registered voter"});
endfunction: unregister_xactor


function void vmm_consensus::register_channel(vmm_channel chan);
   vmm_voter voter;
   if(chan == null) begin
     `vmm_error(this.log,"Trying to register null vmm_channel reference");
     return;
   end
   voter = this.register_voter({"Channel ",
                                chan.log.get_name(), "(",
                                chan.log.get_instance(), ")"});
   voter.channel(chan);
endfunction: register_channel


function void vmm_consensus::unregister_channel(vmm_channel chan);
   `foreach (this.voters,i) begin
      vmm_voter voter = this.voters[i];
      if (voter.get_channel() == chan) begin
         if (!voter.get_vote()) voter.consent("Dead voter consents by default");
         voter.kill_voter();
         this.voters.delete(i);
         return;
      end
   end
   `vmm_error(this.log, {"Channel ", chan.log.get_name(), "(",
                         chan.log.get_instance(),
                         ") is not a registered voter"});
endfunction: unregister_channel


function void vmm_consensus::register_notification(vmm_notify notify,
                                                   int notification);

   vmm_voter voter;
   string    name;
   int       mode;

   if (notify == null) begin
      `vmm_error(this.log, "Cannot register NULL vmm_notify reference");
      return;
   end

   mode = notify.is_configured(notification);
   if (!mode) begin
      `vmm_error(this.log, "Cannot register unconfigured notification");
      return;
   end
   if (mode != vmm_notify::ON_OFF) begin
      `vmm_error(this.log, "Can only register ON_OFF notification");
      return;
   end

   $sformat(name, "Notification #%0d %s(%s)",
            notification, notify.log.get_name(),
            notify.log.get_instance());
   voter = this.register_voter(name);
   voter.notify(notify, notification, 1);
endfunction: register_notification


function void vmm_consensus::register_no_notification(vmm_notify notify,
                                                      int notification);

   vmm_voter voter;
   string    name;
   int       mode;

   if (notify == null) begin
      `vmm_error(this.log, "Cannot register NULL vmm_notify reference");
      return;
   end

   mode = notify.is_configured(notification);
   if (!mode) begin
      `vmm_error(this.log, "Cannot register unconfigured notification");
      return;
   end
   if (mode != vmm_notify::ON_OFF) begin
      `vmm_error(this.log, "Can only register ON_OFF notification");
      return;
   end

   $sformat(name, "Notification #%0d %s(%s)",
            notification, notify.log.get_name(),
            notify.log.get_instance());
   voter = this.register_voter(name);
   voter.notify(notify, notification, 0);
endfunction: register_no_notification


function void vmm_consensus::unregister_notification(vmm_notify notify,
                                                     int notification);
   `foreach (this.voters,i) begin
      vmm_voter voter = this.voters[i];
      if (voter.get_notify() == notify &&
          voter.get_notification() == notification) begin
         if (!voter.get_vote()) voter.consent("Dead voter consents by default");
         voter.kill_voter();
         this.voters.delete(i);
         return;
      end
   end
   begin
      string msg;
      $sformat(msg, "Notification #%0d %s(%s) is not registered with the consensus",
               notification, notify.log.get_name(),
               notify.log.get_instance());
      `vmm_error(this.log, msg);
   end
endfunction: unregister_notification


function void vmm_consensus::register_consensus(vmm_consensus vote,
                                                bit force_through=0);
   vmm_voter voter;
   if(vote == null) begin
     `vmm_error(this.log,"Cannot register NULL vmm_consensus reference");
     return;
   end
   voter = this.register_voter({"Consensus ",
                                vote.log.get_instance()});
   voter.sub_consensus(vote, force_through);
endfunction: register_consensus


function void vmm_consensus::unregister_consensus(vmm_consensus vote);
   `foreach (this.voters,i) begin
      vmm_voter voter = this.voters[i];
      if (voter.get_consensus() == vote) begin
         if (!voter.get_vote()) voter.consent("Dead voter consents by default");
         voter.kill_voter();
         this.voters.delete(i);
         return;
      end
   end
   `vmm_error(this.log, {"Consensus ", vote.log.get_instance(),
                         " is not a registered voter"});
endfunction: unregister_consensus


function void vmm_consensus::unregister_all();
   `foreach (this.voters,i) begin
      vmm_voter voter = this.voters[i];
      voter.kill_voter();
   end
`ifdef VCS2006_06
   // Work-around required by VCS 2006.06
   // but IEEE 1800-2009 compliant
   this.voters.delete();
`else
`ifdef INCA
   this.voters.delete();
`else
   // Works in VCS2008.03 or later
   // IEEE 1800-2005 compliant
   this.voters = '{};
`endif
`endif

   this.n_dissenters = 0;
   this.n_forcing    = 0;
endfunction: unregister_all


task vmm_consensus::wait_for_consensus();
   wait (this.n_forcing > 0 || this.n_dissenters == 0);
endtask: wait_for_consensus


task vmm_consensus::wait_for_no_consensus();
   wait (this.n_forcing == 0 && this.n_dissenters != 0);
endtask: wait_for_no_consensus


function bit vmm_consensus::is_reached();
   return this.n_forcing > 0 || this.n_dissenters == 0;
endfunction: is_reached


function bit vmm_consensus::is_forced();
   return this.n_forcing > 0;
endfunction: is_forced


function string vmm_consensus::psdisplay(string prefix="");
   $sformat(psdisplay, "%sConsensus %s(%s) is %0s", prefix,
            this.log.get_name(), this.log.get_instance(),
            (this.is_reached() ? (this.is_forced() ? "forced" : "reached")
                               : "NOT reached"));
   if (this.voters.size() == 0) begin
      psdisplay = {psdisplay, " by default"};
   end
   else begin
      `foreach (this.voters,i) begin
         vmm_consensus subvote;
         $sformat(psdisplay, "%s\n%s   %s %0s because %s", psdisplay, prefix,
                  this.voters[i].get_name(),
                  (this.voters[i].get_vote() ?
                   (this.voters[i].get_forced() ? "forces" : "consents")
                   : "opposes"),
                  this.voters[i].get_reason());
         subvote = this.voters[i].get_consensus();
         if (subvote != null) begin
            psdisplay = {psdisplay, "\n", subvote.psdisplay({prefix, "      "})};
         end
      end
   end
endfunction: psdisplay


function void vmm_consensus::yeas(ref string who[],
                                  ref string why[]);
   int n = 0;

   `foreach (this.voters,i) begin
      if (this.voters[i].get_vote()) n++;
   end

   who = new [n];
   why = new [n];

   n = 0;
   `foreach (this.voters,i) begin
      if (this.voters[i].get_vote()) begin
         who[n] = this.voters[i].get_name();
         why[n] = this.voters[i].get_reason();
         n++;
      end
   end
endfunction: yeas


function void vmm_consensus::nays(ref string who[],
                                  ref string why[]);
   int n = 0;

   `foreach (this.voters,i) begin
      if (!this.voters[i].get_vote()) n++;
   end

   who = new [n];
   why = new [n];

   n = 0;
   `foreach (this.voters,i) begin
      if (!this.voters[i].get_vote()) begin
         who[n] = this.voters[i].get_name();
         why[n] = this.voters[i].get_reason();
         n++;
      end
   end
endfunction: nays


function void vmm_consensus::forcing(ref string who[],
                                     ref string why[]);
   int n = 0;

   `foreach (this.voters,i) begin
      if (this.voters[i].get_vote() &&
          this.voters[i].get_forced()) n++;
   end

   who = new [n];
   why = new [n];

   n = 0;
   `foreach (this.voters,i) begin
      if (this.voters[i].get_vote() &&
          this.voters[i].get_forced()) begin
         who[n] = this.voters[i].get_name();
         why[n] = this.voters[i].get_reason();
         n++;
      end
   end
endfunction: forcing
   

function void vmm_consensus::XvoteX(bit was_agree,
                                    bit agree,
                                    bit was_forced,
                                    bit forced);
   if (agree && !was_agree) begin
      this.n_dissenters--;
      if (this.n_dissenters == 0) ->this.new_results;
      this.notify.indicate(NEW_VOTE);
   end
   else if (!agree && was_agree) begin
      if (this.n_dissenters == 0) ->this.new_results;
      this.n_dissenters++;
      this.notify.indicate(NEW_VOTE);
   end

   if (forced && !was_forced) begin
      if (this.n_forcing == 0) ->this.new_results;
      this.n_forcing++;
      this.notify.indicate(NEW_VOTE);
   end
   else if (!forced && was_forced) begin
      this.n_forcing--;
      if (this.n_forcing == 0) ->this.new_results;
      this.notify.indicate(NEW_VOTE);
   end

endfunction: XvoteX


function vmm_voter::new(string        name,
                        vmm_consensus vote);
   this.name      = name;
   this.consensus = vote;

   this.vote      = 0;
   this.is_forced = 0;
   this.why       = "Opposes by default";

   this.xactor_voter = null;
   this.channel_voter = null;
   this.sub_vote = null;
endfunction: new


function void vmm_voter::oppose(string why="No reason specified");
   if (this.consensus != null) begin
      this.consensus.XvoteX(this.vote, 0, this.is_forced, 0);
   end
   this.vote = 0;
   this.is_forced = 0;
   this.why = why;
endfunction: oppose


function void vmm_voter::consent(string why="No reason specified");
   if (this.consensus != null) begin
      this.consensus.XvoteX(this.vote, 1, this.is_forced, 0);
   end
   this.vote = 1;
   this.is_forced = 0;
   this.why = why;
endfunction: consent


function void vmm_voter::forced(string why="No reason specified");
   if (this.consensus != null) begin
      this.consensus.XvoteX(this.vote, 1, this.is_forced, 1);
   end
   this.vote = 1;
   this.is_forced = 1;
   this.why = why;
endfunction: forced


function string vmm_voter::get_name();
   return this.name;
endfunction: get_name


function bit vmm_voter::get_vote();
   return this.vote;
endfunction: get_vote


function bit vmm_voter::get_forced();
   return this.is_forced;
endfunction: get_forced


function string vmm_voter::get_reason();
   return this.why;
endfunction: get_reason


function void vmm_voter::xactor(vmm_xactor xact);
   this.xactor_voter = xact;
   if (xact.notify.is_on(vmm_xactor::XACTOR_BUSY)) begin
      this.oppose("Transactor is BUSY");
   end
   else this.consent("Transactor is IDLE");
   fork
      begin
         fork
            begin
               // The transactor might have become busy while
               // the forked thread was getting started...
               if (xact.notify.is_on(vmm_xactor::XACTOR_BUSY)) begin
                  this.oppose("Transactor is BUSY");
               end
               forever begin
                  // Wait for transactor to be IDLE
                  xact.notify.wait_for(vmm_xactor::XACTOR_IDLE);
                  this.consent("Transactor is IDLE");
                  // Prevent an infinite loop
                  if (xact.notify.is_on(vmm_xactor::XACTOR_BUSY)) begin
                     `vmm_fatal(this.xactor_voter.log,
                                "Transactor is indicating both IDLE and BUSY");
                  end
                  // Wait for transactor to be BUSY
                  xact.notify.wait_for(vmm_xactor::XACTOR_BUSY);
                  this.oppose("Transactor is BUSY");
                  // Prevent an infinite loop
                  if (xact.notify.is_on(vmm_xactor::XACTOR_IDLE)) begin
                     `vmm_fatal(this.xactor_voter.log,
                                "Transactor is indicating both IDLE and BUSY");
                  end
               end
            end
         join_none

         @(this.killme);
         disable fork;
      end
   join_none
endfunction: xactor


function void vmm_voter::channel(vmm_channel chan);
   this.channel_voter = chan;
   if (!chan.notify.is_on(vmm_channel::EMPTY)) begin
      this.oppose("Channel is not empty");
   end
   else this.consent("Channel is empty");
   fork
      begin
         fork
            forever begin
               // Wait for channel to be empty
               chan.notify.wait_for(vmm_channel::EMPTY);
               this.consent("Channel is empty");
               // Wait for channel to be not empty
               chan.notify.wait_for_off(vmm_channel::EMPTY);
               this.oppose("Channel is not empty");
            end
         join_none

         @(this.killme);
         disable fork;
      end
   join_none
endfunction: channel


function void vmm_voter::notify(vmm_notify ntfy,
                                int notification,
                                bit is_on);
   this.notify_voter = ntfy;
   this.notification = notification;
   if (is_on) begin
      if (!ntfy.is_on(notification)) begin
         this.oppose("Notification is not indicated");
      end
      else this.consent("Notification is indicated");
   end
   else begin
      if (ntfy.is_on(notification)) begin
         this.oppose("Notification is indicated");
      end
      else this.consent("Notification is not indicated");
   end
   fork
      begin
         fork
            if (is_on) begin
               // Check again as it could have change while
               // the thread was forked
               if (!ntfy.is_on(notification)) begin
                  this.oppose("Notification is not indicated");
               end
               else this.consent("Notification is indicated");

               forever begin
                  // Wait for indication
                  ntfy.wait_for(notification);
                  this.consent("Notification is indicated");
                  // Wait for indication to be reset
                  ntfy.wait_for_off(notification);
                  this.oppose("Notification is not indicated");
               end
            end
            if (!is_on) begin
               // Check again as it could have change while
               // the thread was forked
               if (ntfy.is_on(notification)) begin
                  this.oppose("Notification is indicated");
               end
               else this.consent("Notification is not indicated");

               forever begin
                  // Wait for indication
                  ntfy.wait_for_off(notification);
                  this.consent("Notification is not indicated");
                  // Wait for indication to be reset
                  ntfy.wait_for(notification);
                  this.oppose("Notification is indicated");
               end
            end
         join_none

         @(this.killme);
         disable fork;
      end
   join_none
endfunction: notify


function void vmm_voter::sub_consensus(vmm_consensus vote,
                                       bit force_through);
   this.sub_vote = vote;
   if (!vote.is_reached()) begin
      this.oppose("Sub-consensus is not reached");
   end
   else this.consent("Sub-consensus is reached");

   fork
      begin
         fork
            forever begin
               if (vote.is_forced() && force_through) begin
                  this.forced("Sub-consensus forces");
               end
               else if (vote.is_reached()) this.consent("Sub-consensus consents");
               else this.oppose("Sub-consensus opposes");
               // Wait for sub-consensus to reach new results
               @vote.new_results;
            end
         join_none

         @(this.killme);
         disable fork;
      end
   join_none
endfunction: sub_consensus


function void vmm_voter::kill_voter();
   ->this.killme;
   this.consensus = null;
endfunction: kill_voter


function vmm_xactor vmm_voter::get_xactor();
   return this.xactor_voter;
endfunction: get_xactor


function vmm_channel vmm_voter::get_channel();
   return this.channel_voter;
endfunction: get_channel


function vmm_notify vmm_voter::get_notify();
   return this.notify_voter;
endfunction: get_notify


function int vmm_voter::get_notification();
   return this.notification;
endfunction: get_notification


function vmm_consensus vmm_voter::get_consensus();
   return this.sub_vote;
endfunction: get_consensus


`endif // VMM_CONSENSUS__SV
