// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_component.sv#85 $
//------------------------------------------------------------------------------
//   Copyright 2007-2009 Mentor Graphics Corporation
//   Copyright 2007-2009 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//------------------------------------------------------------------------------

`include "base/ovm_component.svh"
`include "base/ovm_root.svh"

ovm_component ovm_top_levels[$]; // don't use


//------------------------------------------------------------------------------
//
// CLASS- ovm_component
//
//------------------------------------------------------------------------------

// new
// ---

function ovm_component::new (string name, ovm_component parent);
  string error_str;

  super.new(name);

  // If ovm_top, reset name to "" so it doesn't show in full paths then return
  if (parent==null && name == "__top__") begin
    set_name("");
    return;
  end

  // Check that we're not in or past end_of_elaboration
  if (end_of_elaboration_ph.is_in_progress() ||
      end_of_elaboration_ph.is_done() ) begin
    ovm_phase curr_phase;
    curr_phase = ovm_top.get_current_phase();
    ovm_report_fatal("ILLCRT", {"It is illegal to create a component once",
              " phasing reaches end_of_elaboration. The current phase is ", 
              curr_phase.get_name()}, OVM_NONE);
  end

  if (name == "") begin
    name.itoa(m_inst_count);
    name = {"COMP_", name};
  end

  if(parent == this) begin
    ovm_report_fatal("THISPARENT", "cannot set the parent of a component to itself", OVM_NONE);
  end

  if (parent == null)
    parent = ovm_top;

  if(ovm_report_enabled(OVM_MEDIUM+1, OVM_INFO, "NEWCOMP"))
    ovm_report_info("NEWCOMP",$psprintf("this=%0s, parent=%0s, name=%s",
                    this.get_full_name(),parent.get_full_name(),name),OVM_MEDIUM+1);

  if (parent.has_child(name) && this != parent.get_child(name)) begin
    if (parent == ovm_top) begin
      error_str = {"Name '",name,"' is not unique to other top-level ",
      "instances. If parent is a module, build a unique name by combining the ",
      "the module name and component name: $psprintf(\"\%m.\%s\",\"",name,"\")."};
      ovm_report_fatal("CLDEXT",error_str, OVM_NONE);
    end
    else
      ovm_report_fatal("CLDEXT",
        $psprintf("Cannot set '%s' as a child of '%s', %s",
                  name, parent.get_full_name(),
                  "which already has a child by that name."), OVM_NONE);
    return;
  end

  m_parent = parent;

  set_name(name);

  if (!m_parent.m_add_child(this))
    m_parent = null;

  event_pool = new("event_pool");

  
  // Now that inst name is established, reseed (if use_ovm_seeding is set)
  reseed();

  // Do local configuration settings (URM backward compatibility)
  void'(get_config_int("recording_detail", recording_detail));

  // Deprecated container of top-levels (replaced by ovm_top)
  if (parent == ovm_top)
    ovm_top_levels.push_back(this);

  set_report_verbosity_level(ovm_top.get_report_verbosity_level());

  set_report_id_action("CFGOVR", OVM_NO_ACTION);
  set_report_id_action("CFGSET", OVM_NO_ACTION);

//Not sure what ovm_top isn't taking the setting... these two lines should be removed.
  ovm_top.set_report_id_action("CFGOVR", OVM_NO_ACTION);
  ovm_top.set_report_id_action("CFGSET", OVM_NO_ACTION);
endfunction


// m_add_child
// -----------

function bit ovm_component::m_add_child(ovm_component child);

  if (m_children.exists(child.get_name()) &&
      m_children[child.get_name()] != child) begin
      ovm_report_warning("BDCLD",
        $psprintf("A child with the name '%0s' (type=%0s) already exists.",
           child.get_name(), m_children[child.get_name()].get_type_name()), OVM_NONE);
      return 0;
  end

  if (m_children_by_handle.exists(child)) begin
      ovm_report_warning("BDCHLD",
        $psprintf("A child with the name '%0s' %0s %0s'",
                  child.get_name(),
                  "already exists in parent under name '",
                  m_children_by_handle[child].get_name()), OVM_NONE);
      return 0;
    end

  m_children[child.get_name()] = child;
  m_children_by_handle[child] = child;
  return 1;
endfunction


//------------------------------------------------------------------------------
//
// Hierarchy Methods
// 
//------------------------------------------------------------------------------


// get_first_child
// ---------------

function int ovm_component::get_first_child(ref string name);
  return m_children.first(name);
endfunction


// get_next_child
// --------------

function int ovm_component::get_next_child(ref string name);
  return m_children.next(name);
endfunction


// get_child
// ---------

function ovm_component ovm_component::get_child(string name);
  if (m_children.exists(name))
    return m_children[name];
  ovm_report_warning("NOCHILD",{"Component with name '",name,
       "' is not a child of component '",get_full_name(),"'"}, OVM_NONE); 
  return null;
endfunction


// has_child
// ---------

function int ovm_component::has_child(string name);
  return m_children.exists(name);
endfunction


// get_num_children
// ----------------

function int ovm_component::get_num_children();
  return m_children.num();
endfunction


// get_full_name
// -------------

function string ovm_component::get_full_name ();
  // Note- Implementation choice to construct full name once since the
  // full name may be used often for lookups.
  if(m_name == "")
    return get_name();
  else
    return m_name;
endfunction


// get_parent
// ----------

function ovm_component ovm_component::get_parent ();
  return  m_parent;
endfunction


// set_name
// --------

function void ovm_component::set_name (string name);
  
  super.set_name(name);
  m_set_full_name();

endfunction



// m_set_full_name
// ---------------

function void ovm_component::m_set_full_name();
  if (m_parent == ovm_top || m_parent==null)
    m_name = get_name();
  else 
    m_name = {m_parent.get_full_name(), ".", get_name()};

  foreach (m_children[c]) begin
    ovm_component tmp;
    tmp = m_children[c];
    tmp.m_set_full_name(); 
  end

endfunction


// lookup
// ------

function ovm_component ovm_component::lookup( string name );

  string leaf , remainder;
  ovm_component comp;

  comp = this;
  
  m_extract_name(name, leaf, remainder);

  if (leaf == "") begin
    comp = ovm_top; // absolute lookup
    m_extract_name(remainder, leaf, remainder);
  end
  
  if (!comp.has_child(leaf)) begin
    ovm_report_warning("Lookup Error", 
       $psprintf("Cannot find child %0s",leaf), OVM_NONE);
    return null;
  end

  if( remainder != "" )
    return comp.m_children[leaf].lookup(remainder);

  return comp.m_children[leaf];

endfunction


// m_extract_name
// --------------

function void ovm_component::m_extract_name(input string name ,
                                            output string leaf ,
                                            output string remainder );
  int i , len;
  string extract_str;
  len = name.len();
  
  for( i = 0; i < name.len(); i++ ) begin  
    if( name[i] == "." ) begin
      break;
    end
  end

  if( i == len ) begin
    leaf = name;
    remainder = "";
    return;
  end

  leaf = name.substr( 0 , i - 1 );
  remainder = name.substr( i + 1 , len - 1 );

  return;
endfunction
  

// flush
// -----

function void ovm_component::flush();
  return;
endfunction


// do_flush  (flush_hier?)
// --------

function void ovm_component::do_flush();
  foreach( m_children[s] )
    m_children[s].do_flush();
  flush();
endfunction
  

//------------------------------------------------------------------------------
//
// Factory Methods
// 
//------------------------------------------------------------------------------

// create
// ------

function ovm_object  ovm_component::create (string name =""); 
  ovm_report_error("ILLCRT",
    "create cannot be called on a ovm_component. Use create_component instead.", OVM_NONE);
  return null;
endfunction


// clone
// ------

function ovm_object  ovm_component::clone ();
  ovm_report_error("ILLCLN","clone cannot be called on a ovm_component. ", OVM_NONE);
  return null;
endfunction


// print_override_info
// -------------------

function void  ovm_component::print_override_info (string requested_type_name, 
                                                   string name="");
  factory.debug_create_by_name(requested_type_name, get_full_name(), name);
endfunction


// create_component
// ----------------

function ovm_component ovm_component::create_component (string requested_type_name,
                                                        string name);
  return factory.create_component_by_name(requested_type_name, get_full_name(),
                                          name, this);
endfunction


// create_object
// -------------

function ovm_object ovm_component::create_object (string requested_type_name,
                                                  string name="");
  return factory.create_object_by_name(requested_type_name,
                                       get_full_name(), name);
endfunction


// set_type_override (static)
// -----------------

function void ovm_component::set_type_override (string original_type_name,
                                                string override_type_name,
                                                bit    replace=1);
   factory.set_type_override_by_name(original_type_name,
                                     override_type_name, replace);
endfunction 


// set_type_override_by_type (static)
// -------------------------

function void ovm_component::set_type_override_by_type (ovm_object_wrapper original_type,
                                                        ovm_object_wrapper override_type,
                                                        bit    replace=1);
   factory.set_type_override_by_type(original_type, override_type, replace);
endfunction 


// set_inst_override
// -----------------

function void  ovm_component::set_inst_override (string relative_inst_path,  
                                                 string original_type_name,
                                                 string override_type_name);
  string full_inst_path;

  if (relative_inst_path == "")
    full_inst_path = get_full_name();
  else
    full_inst_path = {get_full_name(), ".", relative_inst_path};

  factory.set_inst_override_by_name(
                            original_type_name,
                            override_type_name,
                            full_inst_path);
endfunction 


// set_inst_override_by_type
// -------------------------

function void ovm_component::set_inst_override_by_type (string relative_inst_path,  
                                                        ovm_object_wrapper original_type,
                                                        ovm_object_wrapper override_type);
  string full_inst_path;

  if (relative_inst_path == "")
    full_inst_path = get_full_name();
  else
    full_inst_path = {get_full_name(), ".", relative_inst_path};

  factory.set_inst_override_by_type(original_type, override_type, full_inst_path);

endfunction

//------------------------------------------------------------------------------
//
// Hierarchical report configuration interface
//
//------------------------------------------------------------------------------

// set_report_severity_action_hier
// -------------------------------

function void ovm_component::set_report_severity_action_hier( ovm_severity severity,
                                                              ovm_action action);
  set_report_severity_action(severity, action);
  foreach( m_children[c] )
    m_children[c].set_report_severity_action_hier(severity, action);
endfunction


// set_report_id_action_hier
// -------------------------

function void ovm_component::set_report_id_action_hier( string id, ovm_action action);
  set_report_id_action(id, action);
  foreach( m_children[c] )
    m_children[c].set_report_id_action_hier(id, action);
endfunction


// set_report_severity_id_action_hier
// ----------------------------------

function void ovm_component::set_report_severity_id_action_hier( ovm_severity severity,
                                                                 string id,
                                                                 ovm_action action);
  set_report_severity_id_action(severity, id, action);
  foreach( m_children[c] )
    m_children[c].set_report_severity_id_action_hier(severity, id, action);
endfunction


// set_report_severity_file_hier
// -----------------------------

function void ovm_component::set_report_severity_file_hier( ovm_severity severity,
                                                            OVM_FILE file);
  set_report_severity_file(severity, file);
  foreach( m_children[c] )
    m_children[c].set_report_severity_file_hier(severity, file);
endfunction


// set_report_default_file_hier
// ----------------------------

function void ovm_component::set_report_default_file_hier( OVM_FILE file);
  set_report_default_file(file);
  foreach( m_children[c] )
    m_children[c].set_report_default_file_hier(file);
endfunction


// set_report_id_file_hier
// -----------------------
  
function void ovm_component::set_report_id_file_hier( string id, OVM_FILE file);
  set_report_id_file(id, file);
  foreach( m_children[c] )
    m_children[c].set_report_id_file_hier(id, file);
endfunction


// set_report_severity_id_file_hier
// --------------------------------

function void ovm_component::set_report_severity_id_file_hier ( ovm_severity severity,
                                                                string id,
                                                                OVM_FILE file);
  set_report_severity_id_file(severity, id, file);
  foreach( m_children[c] )
    m_children[c].set_report_severity_id_file_hier(severity, id, file);
endfunction


// set_report_verbosity_level_hier
// -------------------------------

function void ovm_component::set_report_verbosity_level_hier(int verbosity);
  set_report_verbosity_level(verbosity);
  foreach( m_children[c] )
    m_children[c].set_report_verbosity_level_hier(verbosity);
endfunction  


//------------------------------------------------------------------------------
//
// Phase interface 
//
//------------------------------------------------------------------------------


// do_func_phase
// -------------

function void ovm_component::do_func_phase (ovm_phase phase);
  // If in build_ph, don't build if already done
  m_curr_phase = phase;
  if (!(phase == build_ph && m_build_done))
    phase.call_func(this);
endfunction


// do_task_phase
// -------------

task ovm_component::do_task_phase (ovm_phase phase);

  m_curr_phase = phase;
  `ifndef INCA  

    //fork
      //begin
        m_phase_process = process::self();
        phase.call_task(this);
        @m_kill_request;
      //end
    //join

  `else
  // don't use fine grained process control
   fork begin // isolate inner fork so can safely kill via disable fork
     fork : task_phase
       // process 1 - call task; if returns, keep alive until kill request
       begin
         phase.call_task(this);
         @m_kill_request;
       end
       // process 2 - any kill request will preempt process 1
       @m_kill_request;
     join_any
     disable fork;
   end
   join
  `endif

endtask


// do_kill_all
// -----------

function void ovm_component::do_kill_all();
  foreach(m_children[c])
    m_children[c].do_kill_all();
  kill();
endfunction



// kill
// ----

function void ovm_component::kill();
  `ifndef INCA
    if (m_phase_process != null) begin
      m_phase_process.kill;
      m_phase_process = null;
    end
  `else
     ->m_kill_request;
  `endif
endfunction


// suspend
// -------

task ovm_component::suspend();
  `ifndef INCA
  if(m_phase_process != null)
    m_phase_process.suspend;
  `else
  ovm_report_error("UNIMP", "suspend not implemented", OVM_NONE);
  `endif
endtask


// resume
// ------

task ovm_component::resume();
  `ifndef INCA
  if(m_phase_process!=null) 
    m_phase_process.resume;
  `else
   ovm_report_error("UNIMP", "resume not implemented", OVM_NONE);
  `endif
endtask


// restart
// -------

task ovm_component::restart();
  ovm_report_warning("UNIMP",
      $psprintf("%0s: restart not implemented",this.get_name()), OVM_NONE);
endtask


// status
//-------

function string ovm_component::status();

  `ifndef INCA
  process::state ps;

  if(m_phase_process == null)
    return "<unknown>";

  ps = m_phase_process.status();

  return ps.name();
  `else
   ovm_report_error("UNIMP", "status not implemented", OVM_NONE);
  `endif

endfunction


// build
// -----

function void ovm_component::build();
  m_build_done = 1;
  apply_config_settings(print_config_matches);
endfunction


// connect
// -------

function void ovm_component::connect();
  return;
endfunction


// start_of_simulation
// -------------------

function void ovm_component::start_of_simulation();
  return;
endfunction


// end_of_elaboration
// ------------------

function void ovm_component::end_of_elaboration();
  return;
endfunction


// run
// ---

task ovm_component::run();
  return;
endtask


// extract
// -------

function void ovm_component::extract();
  return;
endfunction


// check
// -----

function void ovm_component::check();
  return;
endfunction


// report
// ------

function void ovm_component::report();
  return;
endfunction


// stop
// ----

task ovm_component::stop(string ph_name);
  return;
endtask


// resolve_bindings
// ----------------

function void ovm_component::resolve_bindings();
  return;
endfunction


// do_resolve_bindings
// -------------------

function void ovm_component::do_resolve_bindings();
  foreach( m_children[s] )
    m_children[s].do_resolve_bindings();
  resolve_bindings();
endfunction



//------------------------------------------------------------------------------
//
// Recording interface
//
//------------------------------------------------------------------------------

// accept_tr
// ---------

function void ovm_component::accept_tr (ovm_transaction tr,
                                        time accept_time=0);
  ovm_event e;
  tr.accept_tr(accept_time);
  do_accept_tr(tr);
  e = event_pool.get("accept_tr");
  if(e!=null) 
    e.trigger();
endfunction

// begin_tr
// --------

function integer ovm_component::begin_tr (ovm_transaction tr,
                                          string stream_name ="main",
                                          string label="",
                                          string desc="",
                                          time begin_time=0);
  return m_begin_tr(tr, 0, 0, stream_name, label, desc, begin_time);
endfunction

// begin_child_tr
// --------------

function integer ovm_component::begin_child_tr (ovm_transaction tr,
                                          integer parent_handle=0,
                                          string stream_name="main",
                                          string label="",
                                          string desc="",
                                          time begin_time=0);
  return m_begin_tr(tr, parent_handle, 1, stream_name, label, desc, begin_time);
endfunction

// m_begin_tr
// ----------

function integer ovm_component::m_begin_tr (ovm_transaction tr,
                                          integer parent_handle=0,
                                          bit    has_parent=0,
                                          string stream_name="main",
                                          string label="",
                                          string desc="",
                                          time begin_time=0);
  ovm_event e;
  integer stream_h;
  integer tr_h;
  integer link_tr_h;
  string name;

  tr_h = 0;
  if(has_parent)
    link_tr_h = tr.begin_child_tr(begin_time, parent_handle);
  else
    link_tr_h = tr.begin_tr(begin_time);

  if (tr.get_name() != "")
    name = tr.get_name();
  else
    name = tr.get_type_name();

  if(stream_name == "") stream_name="main";

  if (ovm_verbosity'(recording_detail) != OVM_NONE) begin

    if(m_stream_handle.exists(stream_name))
        stream_h = m_stream_handle[stream_name];

    if (ovm_check_handle_kind("Fiber", stream_h) != 1) 
      begin  
        stream_h = ovm_create_fiber(stream_name, "TVM", get_full_name());
        m_stream_handle[stream_name] = stream_h;
      end

    if(has_parent == 0) 
      tr_h = ovm_begin_transaction("Begin_No_Parent, Link", 
                             stream_h,
                             name,
                             label,
                             desc,
                             begin_time);
    else begin
      tr_h = ovm_begin_transaction("Begin_End, Link", 
                             stream_h,
                             name,
                             label,
                             desc,
                             begin_time);
      if(parent_handle!=0)
        ovm_link_transaction(parent_handle, tr_h, "child");
    end

    m_tr_h[tr] = tr_h;

    if (ovm_check_handle_kind("Transaction", link_tr_h) == 1)
      ovm_link_transaction(tr_h,link_tr_h);
        
    do_begin_tr(tr,stream_name,tr_h); 
        
  end
 
  e = event_pool.get("begin_tr");
  if (e!=null) 
    e.trigger(tr);
        
  return tr_h;

endfunction


// end_tr
// ------

function void ovm_component::end_tr (ovm_transaction tr,
                                     time end_time=0,
                                     bit free_handle=1);
  ovm_event e;
  integer tr_h;
  tr_h = 0;

  tr.end_tr(end_time,free_handle);

  if (ovm_verbosity'(recording_detail) != OVM_NONE) begin

    if (m_tr_h.exists(tr)) begin

      tr_h = m_tr_h[tr];

      do_end_tr(tr, tr_h); // callback

      m_tr_h.delete(tr);

      if (ovm_check_handle_kind("Transaction", tr_h) == 1) begin  

        ovm_default_recorder.tr_handle = tr_h;
        tr.record(ovm_default_recorder);

        ovm_end_transaction(tr_h,end_time);

        if (free_handle)
           ovm_free_transaction_handle(tr_h);

      end
    end
    else begin
      do_end_tr(tr, tr_h); // callback
    end

  end

  e = event_pool.get("end_tr");
  if(e!=null) 
    e.trigger();

endfunction

// record_error_tr
// ---------------

function integer ovm_component::record_error_tr (string stream_name="main",
                                              ovm_object info=null,
                                              string label="error_tr",
                                              string desc="",
                                              time   error_time=0,
                                              bit    keep_active=0);
  string etype;
  integer stream_h;

  if(keep_active) etype = "Error, Link";
  else etype = "Error";

  if(error_time == 0) error_time = $time;

  stream_h = m_stream_handle[stream_name];
  if (ovm_check_handle_kind("Fiber", stream_h) != 1) begin  
    stream_h = ovm_create_fiber(stream_name, "TVM", get_full_name());
    m_stream_handle[stream_name] = stream_h;
  end

  record_error_tr = ovm_begin_transaction(etype, stream_h, label,
                         label, desc, error_time);
  if(info!=null) begin
    ovm_default_recorder.tr_handle = record_error_tr;
    info.record(ovm_default_recorder);
  end

  ovm_end_transaction(record_error_tr,error_time);
endfunction


// record_event_tr
// ---------------

function integer ovm_component::record_event_tr (string stream_name="main",
                                              ovm_object info=null,
                                              string label="event_tr",
                                              string desc="",
                                              time   event_time=0,
                                              bit    keep_active=0);
  string etype;
  integer stream_h;

  if(keep_active) etype = "Event, Link";
  else etype = "Event";

  if(event_time == 0) event_time = $time;

  stream_h = m_stream_handle[stream_name];
  if (ovm_check_handle_kind("Fiber", stream_h) != 1) begin  
    stream_h = ovm_create_fiber(stream_name, "TVM", get_full_name());
    m_stream_handle[stream_name] = stream_h;
  end

  record_event_tr = ovm_begin_transaction(etype, stream_h, label,
                         label, desc, event_time);
  if(info!=null) begin
    ovm_default_recorder.tr_handle = record_event_tr;
    info.record(ovm_default_recorder);
  end

  ovm_end_transaction(record_event_tr,event_time);
endfunction

// do_accept_tr
// ------------

function void ovm_component::do_accept_tr (ovm_transaction tr);
  return;
endfunction


// do_begin_tr
// -----------

function void ovm_component::do_begin_tr (ovm_transaction tr,
                                          string stream_name,
                                          integer tr_handle);
  return;
endfunction


// do_end_tr
// ---------

function void ovm_component::do_end_tr (ovm_transaction tr,
                                        integer tr_handle);
  return;
endfunction


//------------------------------------------------------------------------------
//
// Configuration interface
//
//------------------------------------------------------------------------------


// set_config_int
// --------------

function void  ovm_component::set_config_int    (string      inst_name,
                                                 string      field_name,
                                                 ovm_bitstream_t value);
  ovm_int_config_setting cfg;
  cfg = new(inst_name, field_name, value, this);
  m_config_set = 1;
  m_configuration_table.push_front(cfg);
endfunction


// set_config_string
// -----------------

function void ovm_component::set_config_string  (string      inst_name,  
                                                 string      field_name,
                                                 string      value);
  ovm_string_config_setting cfg;
  cfg = new(inst_name, field_name, value, this);
  m_config_set = 1;
  m_configuration_table.push_front(cfg);
endfunction


// set_config_object
// -----------------

function void ovm_component::set_config_object  (string      inst_name,
                                                 string      field_name,
                                                 ovm_object  value,
                                                 bit         clone=1);
  ovm_object_config_setting cfg;
  if(clone && (value != null)) begin
    ovm_object tmp;
    tmp = value.clone();

    // If create not implemented, or clone is attempted on objects that
    // do not t allow cloning (e.g. components) clone will return null.
    if(tmp == null) begin
      ovm_component comp;
      if ($cast(comp,value)) begin
        ovm_report_error("INVCLNC", {"Clone failed during set_config_object ",
          "with an object that is an ovm_component. Components cannot be cloned."}, OVM_NONE);
        return;
      end
      else begin
        ovm_report_warning("INVCLN", {"Clone failed during set_config_object, ",
          "the original reference will be used for configuration. Check that ",
          "the create method for the object type is defined properly."}, OVM_NONE);
      end
    end
    else
      value = tmp;
  end

  cfg = new(inst_name, field_name, value, this, clone);
  m_config_set = 1;
  m_configuration_table.push_front(cfg);

endfunction


// m_component_path
// ----------------

function void ovm_component::m_component_path(ref ovm_component path[$]);
  ovm_component comp;
  comp = this;
  `ifdef INCA
  path.delete();
  `else
  path = '{};
  `endif
  while(comp != null) begin
    path.push_front(comp);
    comp = comp.get_parent();
  end
endfunction


// m_get_config_matches
// --------------------

function void ovm_component::m_get_config_matches(
      ref ovm_config_setting cfg_matches[$], 
      input ovm_config_setting::ovm_config_type cfgtype, string field_name);
  ovm_component comp;
  static ovm_component stack[$];
  static ovm_config_setting comp_matches[$];

  comp = this;

  `ifdef INCA
  cfg_matches.delete();
  `else
  cfg_matches = '{};
  `endif


  //Get the path up to the root. Since configs are done in groups for a comp,
  //cache the set of config matches from the last check to reduce searching.
  if((stack.size() == 0) || (stack[stack.size()-1] != this) || (m_config_set == 1)) begin
    m_config_set = 0;
    m_component_path(stack);
    `ovm_clear_queue(comp_matches);
    foreach(stack[i]) begin
      for(int j=0; j<stack[i].m_configuration_table.size(); ++j) begin
         if(stack[i].m_configuration_table[j].component_match(this)) 
           comp_matches.push_back(stack[i].m_configuration_table[j]);
      end
    end
  end

  foreach(comp_matches[i]) begin
    if(comp_matches[i].field_match(field_name) &&
         ((comp_matches[i].get_value_type() == cfgtype) ||
          (cfgtype == ovm_config_setting::OVM_UNDEFINED_TYPE))) 
    begin
       cfg_matches.push_back(comp_matches[i]);
    end
  end

endfunction


// check_config_usage
// ------------------

function void ovm_component::check_config_usage ( bit recurse=1 );
  ovm_config_setting cfg;
  bit found;
  string fstr, applied_str, cfg_type;

  found=0; 

  if(recurse)
    foreach(m_children[i])  begin
      m_children[i].check_config_usage(recurse);
    end

  if(m_configuration_table.size() == 0) return;

  if(this == ovm_top)
    fstr = "from the GLOBAL scope";
  else
    fstr = {"from component ", get_full_name(), "(", 
             get_type_name(), ")"};

  foreach(m_configuration_table[i]) begin
    cfg = m_configuration_table[i];
    if(cfg.m_used_list.size() == 0 &&
       cfg.m_override_list.size() == 0 )
    begin
      if(cfg.get_value_type() == ovm_config_setting::OVM_INT_TYPE)
        cfg_type = "int";
      else if(cfg.get_value_type() == ovm_config_setting::OVM_STRING_TYPE)
        cfg_type = "string";
      else
        cfg_type = "object";
      ovm_report_warning("CFGNTS", {"No get_config_",cfg_type,
         "() call ever matched the following set_config_", cfg_type, "() call ", fstr,
         ": ", cfg.convert2string()}, OVM_NONE);
    end 
  end

  //Do not do the lookup work if the CFGOVR action is off
  if(ovm_report_enabled(OVM_LOW, OVM_INFO, "CFGOVR"))
  foreach(m_configuration_table[i]) begin
    cfg = m_configuration_table[i];
    if(cfg.m_override_list.size() != 0)
    begin
      ovm_report_info("CFGOVR", {"The configuration setting ", cfg.convert2string(), " ", fstr, " was overridden by config setting ", cfg.m_override_list[0].convert2string(), " from component ", cfg.m_override_list[0].m_from.get_full_name(), "(",  cfg.m_override_list[0].m_from.get_type_name(), ")"}, OVM_NONE);
    end
  end

  //Do not do the lookup work if the CFGSET action is off
  if(ovm_report_enabled(OVM_LOW, OVM_INFO, "CFGSET"))
  foreach(m_configuration_table[i]) begin
    string cfgstr;
    cfg = m_configuration_table[i];
    if(cfg.m_used_list.size() != 0)
      begin
        cfgstr = cfg.convert2string();
        applied_str = "";
        for(int j=0; j<cfg.m_used_list.size(); ++j) begin
          ovm_report_info("CFGSET", {"The configuration setting ", cfgstr, " ", fstr, " was applied to component: ", cfg.m_used_list[j].get_full_name(), " (",  cfg.m_used_list[j].get_type_name(), ")"}, OVM_NONE);
        end
      end 
  end

endfunction


// get_config_int
// --------------

function bit ovm_component::get_config_int (string field_name,
                                            inout ovm_bitstream_t value);
  static ovm_config_setting cfg_matches[$];
  ovm_int_config_setting cfg;
  ovm_component c;
  //Scan the config tables of each component in the path
  m_get_config_matches(cfg_matches, ovm_config_setting::OVM_INT_TYPE, field_name);

  //The first match is the override
  if(cfg_matches.size()) begin
    $cast(cfg, cfg_matches[0]);
    if(print_config_matches)
      cfg_matches[0].print_match(this, cfg_matches[0].get_from_component(), field_name);
    cfg_matches[0].set_used(this);
    for(int i=1; i<cfg_matches.size(); ++i) begin
      cfg_matches[i].set_override(cfg_matches[0]);
    end
    value = cfg.m_value;
    return 1;
  end

  return 0;
endfunction
  

// get_config_string
// -----------------

function bit ovm_component::get_config_string (string field_name,
                                               inout string value);
  static ovm_config_setting cfg_matches[$];
  ovm_string_config_setting cfg;
  ovm_component c;

  //Scan the config tables of each component in the path
  m_get_config_matches(cfg_matches, ovm_config_setting::OVM_STRING_TYPE, field_name);

  //The first match is the override
  if(cfg_matches.size()) begin
    $cast(cfg, cfg_matches[0]);
    if(print_config_matches)
      cfg_matches[0].print_match(this, cfg_matches[0].get_from_component(), field_name);
    cfg_matches[0].set_used(this);
    for(int i=1; i<cfg_matches.size(); ++i)
      cfg_matches[i].set_override(cfg_matches[0]);
    value = cfg.m_value;
    return 1;
  end

  return 0;
endfunction

  
// get_config_object
// -----------------

function bit ovm_component::get_config_object (string field_name,
                                               inout ovm_object value,  
                                               input bit clone=1);
  static ovm_config_setting cfg_matches[$];
  ovm_object_config_setting cfg;
  ovm_component c;

  //Scan the config tables of each component in the path
  m_get_config_matches(cfg_matches, ovm_config_setting::OVM_OBJECT_TYPE, field_name);

  //The first match is the override
  if(cfg_matches.size()) begin
    $cast(cfg, cfg_matches[0]);
    if(print_config_matches)
      cfg_matches[0].print_match(this, cfg_matches[0].get_from_component(), field_name);
    cfg_matches[0].set_used(this);
    for(int i=1; i<cfg_matches.size(); ++i)
      cfg_matches[i].set_override(cfg_matches[0]);
    if((clone && cfg.m_clone) && (cfg.m_value != null))
      value = cfg.m_value.clone();
    else
      value = cfg.m_value;
    return 1;
  end

  return 0;
endfunction
 

// apply_config_settings
// ---------------------

function void ovm_component::apply_config_settings (bit verbose=0);
  static ovm_component stack[$];
  static ovm_config_setting overrides[string];
  ovm_config_setting cfg;
  ovm_int_config_setting cfg_int;
  ovm_string_config_setting cfg_str;
  ovm_object_config_setting cfg_obj;
  ovm_component comp;
  string match_str;
  string matched="";
  bit has_match=0;
  if(stack.size() == 0 || stack[stack.size()-1] != this) begin
    m_component_path(stack);
  end
  //apply any override that matches this component. Go bottom up and then back
  //to front so the last override in the global scope has precedence to the
  //first override in the parent scope.
  if (verbose) begin
    match_str = {"Auto-configuration matches for component ",
       this.get_full_name()," (",get_type_name(),"). Last entry for a given field takes precedence.\n\n",
       "   Config set from  Instance Path     Field name   Type    Value\n",
       "   ------------------------------------------------------------------------------\n"};
  end
  for(int i=stack.size()-1; i>=0; --i) begin
    comp = stack[i];
    if(comp == null) comp = ovm_top;
    if(comp!=null) begin
      for(int j=comp.m_configuration_table.size()-1; j>=0; --j) begin
        cfg = comp.m_configuration_table[j];
        if(cfg.component_match(this)) begin
          if(verbose)
            matched = cfg.matches_string(this,comp);
          if($cast(cfg_int, cfg))
             set_int_local(cfg_int.m_field, cfg_int.m_value);
          else if($cast(cfg_str, cfg))
            set_string_local(cfg_str.m_field, cfg_str.m_value);
          else if($cast(cfg_obj, cfg)) begin
            set_object_local(cfg_obj.m_field, cfg_obj.m_value, cfg_obj.m_clone);
            if(verbose)
              matched = {matched, " clone=",(cfg_obj.m_clone==1)?"1":"0"};
          end
          if(verbose)
            match_str = {match_str, "  ", matched,"\n"};
          has_match = 1;
          if(m_sc.status)
            cfg.m_used_list.push_back(this);
        end
      end
    end
  end

  if (verbose && has_match)
    if(ovm_report_enabled(OVM_MEDIUM, OVM_INFO, "auto-configuration"))
      ovm_report_info("auto-configuration", {match_str,"\n"}, OVM_MEDIUM);

endfunction


// print_config_settings
// ---------------------

function void ovm_component::print_config_settings (string field="",
                                                    ovm_component comp=null,
                                                    bit recurse=0);
  static int depth;
  static ovm_component stack[$];
  ovm_component cc;
  string all_matches;
  string v,r;
  all_matches = "";

  if(comp==null)
    comp = this;

  comp.m_component_path(stack);
  while(stack.size() && (stack[stack.size()-1] != comp))
    void'(stack.pop_back());

  cc = comp;

  $swrite(v, "%s", cc.get_full_name());
  while(v.len()<17) v = {v," "};
  foreach(stack[s]) begin
    comp = stack[s];
    for(int i=0; i<comp.m_configuration_table.size(); ++i) begin
      r = comp.m_configuration_table[i].matches_string(cc, comp);
      if(r != "")
        all_matches = {all_matches, v, r, "\n"};
    end
  end

  // Note- should use ovm_printer for formatting
  if(((all_matches != "") || (recurse == 1)) && depth == 0) begin
    $display("Configuration settings for component %s (recurse = %0d)",
             cc.get_full_name(), recurse);
    $display("Set to            Set from         Component match   Field name   Type    Value");
    $display("-------------------------------------------------------------------------------");
  end
  if(all_matches == "")
    $display("%s NONE", v);
  else
    $write("%s", all_matches);

  if(recurse) begin
    depth++;
    if(cc.m_children.first(v))
      do this.print_config_settings(field, cc.m_children[v], recurse);
      while(cc.m_children.next(v));
    depth--;
  end
endfunction

//------------------------------------------------------------------------------
//
// DEPRECATED - DO NOT USE
//
//------------------------------------------------------------------------------

// global_stop_request (static, deprecated)
// -------------------

function void ovm_component::global_stop_request();
  ovm_root top;
  top = ovm_root::get();
  top.stop_request();
endfunction


// post_new (deprecated)
// --------

function void ovm_component::post_new();
  return;
endfunction


// export_connections (deprecated)
// ------------------

function void ovm_component::export_connections();
  return;
endfunction


// import_connections (deprecated)
// ------------------

function void ovm_component::import_connections();
  return;
endfunction


// configure (deprecated)
// ---------

function void ovm_component::configure();
  return;
endfunction


// pre_run (deprecated)
// -------

function void ovm_component::pre_run();
  return;
endfunction


// find_component (deprecated)
// --------------

function ovm_component ovm_component::find_component (string comp_match);
  static bit issued=0;
  if (!issued) begin
    issued=1;
    ovm_top.ovm_report_warning("deprecated",
      {"ovm_component::find_component() is deprecated and replaced by ",
      "ovm_top.find()"}, OVM_NONE);
  end
  return ovm_top.find(comp_match);
endfunction


// find_components (deprecated)
// ---------------

function void ovm_component::find_components (string comp_match,
                                              ref ovm_component comps[$]);
  static bit issued=0;
  if (!issued) begin
    issued=1;
    ovm_top.ovm_report_warning("deprecated",
      {"ovm_component::find_components() is deprecated and replaced by ",
      "ovm_top.find_all()"}, OVM_NONE);
  end
  ovm_top.find_all(comp_match,comps);
endfunction


// get_component (deprecated)
// -------------

function ovm_component ovm_component::get_component (int ele);
  ovm_component m__comps[$];
  static bit issued=0;
  if (!issued) begin
    issued=1;
    ovm_top.ovm_report_warning("deprecated",
      {"ovm_component::get_component() is an internal method that has been ",
      "deprecated. ovm_top's find, find_all, and ovm_component's lookup ",
      "method provide similar functionality."}, OVM_NONE);
  end
  if (m__comps.size()==0)
    ovm_top.find_all("*",m__comps);
  if (ele < m__comps.size())
    return m__comps[ele];
  return null;
endfunction


// get_num_components (deprecated)
// ------------------

function int ovm_component::get_num_components ();
  ovm_component m__comps[$]; 
  static bit issued=0;
  if (!issued) begin
    issued=1;
    ovm_top.ovm_report_warning("deprecated",
      {"ovm_component::get_num_components() is an internal method that has ",
      "been deprecated. The number of components in the testbench can be ",
      "obtained using the ovm_top.find_all() method."}, OVM_NONE);
  end
  while (m__comps.size()!=0)
    m__comps.delete(0);
  ovm_top.find_all("*",m__comps);
  get_num_components = m__comps.size();
endfunction

