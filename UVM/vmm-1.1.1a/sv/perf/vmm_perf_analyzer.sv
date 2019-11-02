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


`ifndef VMM_PERF_ANALYZER__SV
`define VMM_PERF_ANALYZER__SV

`include "vmm.sv"
`include "perf/vmm_perf_tenure.sv"
`include "perf/vmm_sql.sv"

class vmm_perf_data;
   time start_time;
   time end_time;
   time resume_time;
   time active_time = 0;
   string more_data;

   bit  aborted;

   vmm_perf_tenure tenure;
endclass: vmm_perf_data


typedef class vmm_perf_analyzer;


class vmm_perf_analyzer_callbacks;
   virtual function void analyze_tenure(vmm_perf_analyzer analyzer,
                                        vmm_perf_tenure   tenure,
                                        ref time          start_time,
                                        ref time          end_time,
                                        ref time          active_time,
                                        ref bit           aborted,
                                        ref string        more_data,
                                        ref bit           filtered);
   endfunction
endclass


class vmm_perf_analyzer;

   typedef enum {SOFT, HARD} reset_e;

   vmm_log log;

   local int unsigned max_n_initiators;
   local int unsigned max_n_targets;
   local int unsigned max_n_concurrent;

   local int unsigned known_initiators[*];
   local int unsigned known_targets[*];

   local vmm_perf_data active[$];
   local vmm_perf_data suspended[$];
   local vmm_perf_data completed[$];

   local vmm_sql_table sql_table;
   local string        user_schema;

   local vmm_perf_analyzer_callbacks cbs[$];

   // For simple report
   local time min_time;
   local time max_time;
   local time active_time;
   local time min_abort_time;
   local time max_abort_time;
   local time abort_time;
   local int  n;

   extern function new(string       name             = "",
                       vmm_sql_db   sql_db,
                       int unsigned max_n_initiators = 0,
                       int unsigned max_n_targets    = 0,
                       int unsigned max_n_concurrent = 1,
                       string user_schema = "");

   extern virtual function time now();

   extern function void start_tenure(vmm_perf_tenure tenure);
   extern function void suspend_tenure(vmm_perf_tenure tenure);
   extern function void resume_tenure(vmm_perf_tenure tenure);
   extern function void end_tenure(vmm_perf_tenure tenure,
                                   string more_data = "");
   extern function void abort_tenure(vmm_perf_tenure tenure,
                                     string more_data = "");
   extern function bit add_tenure(int      initiator_id = -1,
                                  int      target_id    = -1,
                                  time     start_time,
                                  time     end_time,
                                  vmm_data tr           = null,
                                  time     active_time  = 0,
                                  bit      aborted      = 0,
                                  string   more_data    = "");

   extern virtual function string psdisplay(string prefix = "");
   extern function void report(string name         = "",
                               bit    brief        = 1);

   extern function vmm_sql_db get_db();
   extern function void save_db();
   extern function void save_db_txt(string name = "");

   extern function void reset(reset_e rst_typ = SOFT);

   extern function void append_callback(vmm_perf_analyzer_callbacks cb);
   extern function void prepend_callback(vmm_perf_analyzer_callbacks cb);
   extern function void unregister_callback(vmm_perf_analyzer_callbacks cb);
endclass: vmm_perf_analyzer

function vmm_perf_analyzer::new(string       name             = "",
                                vmm_sql_db   sql_db,
                                int unsigned max_n_initiators = 0,
                                int unsigned max_n_targets = 0,
                                int unsigned max_n_concurrent = 1,
                                string user_schema = "");
   string schema;

   this.log = new("Performance Analyzer", name);

   this.max_n_initiators = max_n_initiators;
   this.max_n_targets = max_n_targets;

   this.max_n_concurrent = max_n_concurrent;
   if (this.max_n_concurrent == 0) this.max_n_concurrent = (1<<31)-1;

   schema = "tenureID integer, initiatorID integer, targetID integer, start bigint, end bigint, active bigint, Abort tinyint";
   this.user_schema = user_schema;
   if (user_schema != "") schema = {schema, ", ", user_schema};
   this.sql_table = sql_db.create_table(name, schema, 0);

   this.active_time = 0;
   this.abort_time = 0;
   this.max_time = 0;
   this.min_time = '1;
   this.max_abort_time = 0;
   this.min_abort_time = '1;
   this.n = 0;
endfunction: new


function time vmm_perf_analyzer::now();
   return $time;
endfunction: now


function void vmm_perf_analyzer::start_tenure(vmm_perf_tenure tenure);
   vmm_perf_data datum;

   if (tenure == null) begin
      `vmm_error(this.log, "Attempting to start a NULL tenure");
      return;
   end

   `foreach (this.active,i) begin
      if (this.active[i].tenure == tenure) begin
         `vmm_error(this.log, {"Attempting to start an already-active tenure: ",
                               tenure.psdisplay()});
         return;
      end
   end

   if (this.max_n_initiators > 0) begin
      if (!this.known_initiators.exists(tenure.get_initiator_id())) begin
         this.known_initiators[tenure.get_initiator_id()] = 1;
         if (this.known_initiators.num() > this.max_n_initiators) begin
            `vmm_error(this.log, $psprintf("Too many initiators: %0d > %0d",
                                           this.known_initiators.num(),
                                           this.max_n_initiators));
         end
      end
   end

   if (this.max_n_targets > 0) begin
      if (!this.known_targets.exists(tenure.get_initiator_id())) begin
         this.known_targets[tenure.get_target_id()] = 1;
         if (this.known_targets.num() > this.max_n_targets) begin
            `vmm_error(this.log, $psprintf("Too many targets: %0d > %0d",
                                           this.known_targets.num(),
                                           this.max_n_targets));
         end
      end
   end

   datum = new;
   datum.tenure = tenure;

   datum.start_time = this.now();
   datum.resume_time = datum.start_time;

   this.active.push_back(datum);

   if (this.active.size() > this.max_n_concurrent) begin
      `vmm_error(this.log, $psprintf("Too many active tenures: %0d > %0d",
                                     this.active.size(), this.max_n_concurrent));
      `foreach (this.active,i) begin
         `vmm_debug(this.log, this.active[i].tenure.psdisplay("Active: "));
      end
   end
endfunction: start_tenure


function void vmm_perf_analyzer::suspend_tenure(vmm_perf_tenure tenure);
   if (tenure == null) begin
      `vmm_error(this.log, "Attempting to suspend a NULL tenure");
      return;
   end

   `foreach (this.active,i) begin
      if (this.active[i].tenure == tenure) begin
         vmm_perf_data datum = this.active[i];

         this.active.delete(i);
         this.suspended.push_back(datum);
         datum.active_time += this.now() - datum.resume_time;

         return;
      end
   end

   `vmm_error(this.log, {"Attempting to suspend a non-active tenure: ",
                         tenure.psdisplay()});
endfunction: suspend_tenure


function void vmm_perf_analyzer::resume_tenure(vmm_perf_tenure tenure);
   if (tenure == null) begin
      `vmm_error(this.log, "Attempting to resume a NULL tenure");
      return;
   end

   `foreach (this.suspended,i) begin
      if (this.suspended[i].tenure == tenure) begin
         vmm_perf_data datum = this.suspended[i];

         this.suspended.delete(i);
         this.active.push_back(datum);

         datum.resume_time = datum.start_time;

         if (this.active.size() > this.max_n_concurrent) begin
            `vmm_error(this.log, $psprintf("Too many active tenures: %0d > %0d",
                                           this.active.size(), this.max_n_concurrent));
         end
         return;
      end
   end
   `vmm_error(this.log, {"Attempting to resume a non-suspended tenure: ",
                         tenure.psdisplay()});
endfunction: resume_tenure


function void vmm_perf_analyzer::end_tenure(vmm_perf_tenure tenure, 
                                            string          more_data = "");
   if (tenure == null) begin
      `vmm_error(this.log, "Attempting to end a NULL tenure");
      return;
   end

   `foreach (this.active,i) begin
      if (this.active[i].tenure == tenure) begin
         vmm_perf_data datum = this.active[i];
         bit filtered = 0;

         this.active.delete(i);

         datum.end_time = this.now();
         datum.active_time += this.now() - datum.resume_time;
         datum.aborted = 0;
         datum.more_data = more_data;

         `foreach (this.cbs,i) begin
            this.cbs[i].analyze_tenure(this,
                                       datum.tenure,
                                       datum.start_time,
                                       datum.end_time,
                                       datum.active_time,
                                       datum.aborted,
                                       datum.more_data,
                                       filtered);
         end

         if (filtered) return;

         if (datum.end_time < datum.start_time) begin
            `vmm_warning(this.log, $psprintf("Tenure modified with end time (%0d) < start time (%0d)", datum.end_time, datum.start_time));
            return;
         end

         if (datum.active_time > datum.end_time - datum.start_time) begin
            `vmm_error(this.log, $psprintf("Tenure modified with active time (%0d) > end time - start time (%0d)", datum.active_time, datum.end_time - datum.start_time));
            return;
         end

         this.completed.push_back(datum);

         this.active_time += datum.active_time;
         if (this.min_time > datum.active_time) this.min_time = datum.active_time;
         if (this.max_time < datum.active_time) this.max_time = datum.active_time;
         this.n++;

         return;
      end
   end

   `vmm_error(this.log, {"Attempting to end a non-active tenure: ",
                         tenure.psdisplay()});
endfunction: end_tenure


function void vmm_perf_analyzer::abort_tenure(vmm_perf_tenure tenure,
                                              string          more_data = "");
   if (tenure == null) begin
      `vmm_error(this.log, "Attemtping to abort a NULL tenure");
      return;
   end

   `foreach (this.active,i) begin
      if (this.active[i].tenure == tenure) begin
         vmm_perf_data datum = this.active[i];
         bit filtered = 0;

         this.active.delete(i);

         datum.end_time = this.now();
         datum.active_time += this.now() - datum.resume_time;
         datum.aborted = 1;
         datum.more_data = more_data;

         `foreach (this.cbs,i) begin
            this.cbs[i].analyze_tenure(this,
                                       datum.tenure,
                                       datum.start_time,
                                       datum.end_time,
                                       datum.active_time,
                                       datum.aborted,
                                       datum.more_data,
                                       filtered);
         end

         if (filtered) return;

         if (datum.end_time < datum.start_time) begin
            `vmm_warning(this.log, $psprintf("Tenure modified with end time (%0d) < start time (%0d)", datum.end_time, datum.start_time));
            return;
         end

         if (datum.active_time > datum.end_time - datum.start_time) begin
            `vmm_error(this.log, $psprintf("Tenure modified with active time (%0d) > end time - start time (%0d)", datum.active_time, datum.end_time - datum.start_time));
            return;
         end

         this.completed.push_back(datum);

         this.active_time += datum.active_time;
         if (this.min_time > datum.active_time) this.min_time = datum.active_time;
         if (this.max_time < datum.active_time) this.max_time = datum.active_time;

         this.abort_time += datum.active_time;
         if (this.min_abort_time > datum.active_time) this.min_abort_time = datum.active_time;
         if (this.max_abort_time < datum.active_time) this.max_abort_time = datum.active_time;
         this.n++;

         return;
      end
   end

   `vmm_error(this.log, {"Attempting to abort a non-active tenure: ",
                         tenure.psdisplay()});
endfunction: abort_tenure


function bit vmm_perf_analyzer::add_tenure(int      initiator_id = -1,
                                           int      target_id = -1,
                                           time     start_time,
                                           time     end_time,
                                           vmm_data tr = null,
                                           time     active_time = 0,
                                           bit      aborted = 0,
                                           string   more_data = "");
   if (end_time < start_time) begin
      `vmm_error(this.log, $psprintf("Attempting to add tenure with end time (%0d) < start time (%0d)", end_time, start_time));
      return 0;
   end

   if (active_time > end_time - start_time) begin
      `vmm_error(this.log, $psprintf("Attempting to add tenure with active time (%0d) > end time - start time (%0d)", active_time, end_time - start_time));
      return 0;
   end

   if (active_time == 0) active_time = end_time - start_time;

   begin
      vmm_perf_tenure tenure = new(initiator_id, target_id, tr);
      bit             filtered = 0;

      `foreach (this.cbs,i) begin
         this.cbs[i].analyze_tenure(this,
                                    tenure,
                                    start_time,
                                    end_time,
                                    active_time,
                                    aborted,
                                    more_data,
                                    filtered);
      end

      if (filtered) return 1;

      if (end_time < start_time) begin
         `vmm_error(this.log, $psprintf("Tenure modified with end time (%0d) < start time (%0d)", end_time, start_time));
         return 0;
      end

      if (active_time > end_time - start_time) begin
         `vmm_error(this.log, $psprintf("Tenure modified with active time (%0d) > end time - start time (%0d)", active_time, end_time - start_time));
         return 0;
      end

      begin
         vmm_perf_data   datum = new;

         datum.tenure      = tenure;
         datum.start_time  = start_time;
         datum.end_time    = end_time;
         datum.active_time = active_time;
         datum.aborted     = aborted;
         datum.more_data   = more_data;

         this.completed.push_back(datum);

         this.active_time += datum.active_time;
         if (this.min_time > datum.active_time) this.min_time = datum.active_time;
         if (this.max_time < datum.active_time) this.max_time = datum.active_time;

         if (aborted) begin
            this.abort_time += datum.active_time;
            if (this.min_abort_time > datum.active_time) this.min_abort_time = datum.active_time;
            if (this.max_abort_time < datum.active_time) this.max_abort_time = datum.active_time;
         end
         this.n++;

      end
   end

   return 1;
endfunction: add_tenure


function string vmm_perf_analyzer::psdisplay(string prefix = "");
   $sformat(psdisplay, "%s-- Performance Analyzer Status --", prefix);
   $sformat(psdisplay, "%s\n%sMax init/targ/conc = %0d/%0d/%0d",
            psdisplay, prefix, this.max_n_initiators, this.max_n_targets,
            this.max_n_concurrent);
   $sformat(psdisplay, "%s\n%sActive tenures:", psdisplay, prefix);
   `foreach (this.active,i) begin
      $sformat(psdisplay, "%s\n%s", psdisplay, this.active[i].tenure.psdisplay({prefix, "   "}));
   end
   $sformat(psdisplay, "%s\n%sSuspended tenures:", psdisplay, prefix);
   `foreach (this.suspended,i) begin
      $sformat(psdisplay, "%s\n%s", psdisplay, this.suspended[i].tenure.psdisplay({prefix, "   "}));
   end
endfunction: psdisplay


function void vmm_perf_analyzer::report(string name = "",
                                        bit    brief = 1);
   int fp = 32'h8000_0001; // STDOUT

   if (name != "") begin
      fp = $fopen(name, "w");
      if (!fp) begin
         `vmm_error(this.log, {"Unable to open ", name, " for writing."});
         return;
      end
   end
   
   $fwrite(fp, "\nPerformance Analysis Report for %s (based on %0d data points)\n", this.log.get_instance(), n);
   $fwrite(fp, "====================================================================\n");
   $fwrite(fp, "                            All Completed  |              Aborted\n");

   $fwrite(fp, "Min Tenure Duration: %d  | %d\n",
           this.min_time, this.min_abort_time);
   $fwrite(fp, "Avg Tenure Duration: %d  | %d\n",
           this.active_time / n, this.abort_time / n);
   $fwrite(fp, "Max Tenure Duration: %d  | %d\n",
           this.max_time, this.max_abort_time);
   $fwrite(fp, "Utilization        : %d%% | %d%%\n",
           (this.active_time * 100) / this.now(),
           (this.abort_time * 100) / this.now());

   if (name != "") begin
      $fclose(fp);
   end

   if (this.active.size() != 0 ||
       this.suspended.size() != 0) begin
      `vmm_warning(this.log, $psprintf("There are %0d active/suspended tenures not included in the report",
                   this.active.size() + this.suspended.size()));
   end
endfunction: report

function vmm_sql_db vmm_perf_analyzer::get_db();
   return this.sql_table.get_db();
endfunction: get_db

function void vmm_perf_analyzer::save_db();
   `foreach (this.completed,i) begin
      vmm_perf_data   datum  = this.completed[i];
      vmm_perf_tenure tenure = datum.tenure;
      string row;

      $sformat(row, "%0d,%0d,%0d,%0d,%0d,%0d,%b",
	       tenure.get_tenure_id(),
	       tenure.get_initiator_id(), 
	       tenure.get_target_id(),
	       datum.start_time, 
	       datum.end_time, 
	       datum.active_time, 
	       datum.aborted);

      if (this.user_schema != "") row = {row, ",", datum.more_data};

      this.sql_table.insert(row);
   end
   `ifdef INCA
   this.completed.delete();
   `else
   this.completed = '{};
   `endif

   begin
      vmm_sql_db sql_db = this.sql_table.get_db();
      sql_db.commit();
   end

   if (this.active.size() != 0 ||
       this.suspended.size() != 0) begin
      `vmm_warning(this.log, $psprintf("There are %0d active/suspended tenures not included in the report",
                   this.active.size() + this.suspended.size()));
   end
endfunction: save_db

function void vmm_perf_analyzer::save_db_txt(string name = "");
   int fp;

   if (name == "") begin
      name = {this.log.get_instance(), ".perf.db"};
   end
   
   fp = $fopen(name, "w");
   if (!fp) begin
      `vmm_error(this.log, {"Unable to open ", name, " for writing."});
      return;
   end

   $fwrite(fp,"TenureID InitiatorID TargetID Start End Active Abort\n");
   `foreach (this.completed,i) begin
      vmm_perf_data   datum  = this.completed[i];
      vmm_perf_tenure tenure = datum.tenure;

      $fwrite(fp, "%0d %0d %0d %0d %0d %0d %b\n", tenure.get_tenure_id(),
              tenure.get_initiator_id(), tenure.get_target_id(),
              datum.start_time, datum.end_time, datum.active_time, datum.aborted);
   end

   $fclose(fp);

   if (this.active.size() != 0 ||
       this.suspended.size() != 0) begin
      `vmm_warning(this.log, $psprintf("There are %0d active/suspended tenures not included in the DB",
                   this.active.size() + this.suspended.size()));
   end
endfunction: save_db_txt

function void vmm_perf_analyzer::reset(reset_e rst_typ = SOFT);
   this.known_initiators.delete();
   this.known_targets.delete();
   `ifdef INCA
     this.active.delete();
     this.completed.delete();
   `else
     this.active = '{};
     this.completed = '{};
   `endif
   begin
     vmm_sql_db sql_db = this.sql_table.get_db();
     sql_db.statement(
         $psprintf(
             "DELETE FROM TABLE %s;",
             this.sql_table.get_tblname())
         );
   end

   this.active_time = 0;
   this.abort_time = 0;
   this.max_time = 0;
   this.min_time = '1;
   this.max_abort_time = 0;
   this.min_abort_time = '1;
   this.n = 0;

   if (rst_typ == HARD) begin
     `ifdef INCA
        this.cbs.delete();
     `else
        this.cbs = '{};
     `endif
   end
endfunction: reset


function void vmm_perf_analyzer::append_callback(vmm_perf_analyzer_callbacks cb);
   `foreach (this.cbs,i) begin
      if (this.cbs[i] == cb) begin
         `vmm_warning(this.log, "Callback has already been registered");
         return;
      end
   end
   
   // Append new callback
   this.cbs.push_back(cb);
endfunction: append_callback


function void vmm_perf_analyzer::prepend_callback(vmm_perf_analyzer_callbacks cb);
   `foreach (this.cbs,i) begin
      if (this.cbs[i] == cb) begin
         `vmm_warning(this.log, "Callback has already been registered");
         return;
      end
   end
   
   // Prepend new callback
   this.cbs.push_front(cb);
endfunction: prepend_callback


function void vmm_perf_analyzer::unregister_callback(vmm_perf_analyzer_callbacks cb);
   `foreach (this.cbs,i) begin
      if (this.cbs[i] == cb) begin
         int j = i;
         // Unregister it
         this.cbs.delete(j);
         return;
      end
   end

   `vmm_warning(this.log, "Callback was not registered");
endfunction: unregister_callback

`endif // VMM_PERF_ANALYZER__SV
