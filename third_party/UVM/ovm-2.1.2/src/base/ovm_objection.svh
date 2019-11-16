//----------------------------------------------------------------------
//   Copyright 2007-2011 Mentor Graphics Corp.
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
//----------------------------------------------------------------------

`ifndef OVM_OBJECTION_SVH
`define OVM_OBJECTION_SVH

//Assumes access to ovm via an import of ovm_pkg or `include of ovm.svh

typedef class ovm_objection;
typedef class ovm_sequence_base;


//------------------------------------------------------------------------------
//
// Class: ovm_objection
//
//------------------------------------------------------------------------------
// Objections provide a facility for coordinating status information between
// two or more participating components, objects, and even module-based IP.
// In particular, the ~ovm_test_done~ built-in objection provides a means for
// coordinating when to end a test, i.e. when to call <global_stop_request> to
// end the <ovm_component::run> phase.  When all participating components have
// dropped their raised objections with ~ovm_test_done~, an implicit call to
// ~global_stop_request~ is issued.
//------------------------------------------------------------------------------

class ovm_objection extends ovm_report_object;

  protected int  m_source_count[ovm_object];
  protected int  m_total_count [ovm_object];
  protected time m_drain_time  [ovm_object];
  protected bit  m_draining    [ovm_object];

  protected bit m_hier_mode = 1;

  ovm_root top = ovm_root::get();

  // Function: new
  //
  // Creates a new objection instance.

  function new(string name="");
    super.new(name);
    set_report_verbosity_level(top.get_report_verbosity_level());
  endfunction


  // Function- m_report
  //
  // Internal method for reporting count updates

  function void m_report(ovm_object obj, ovm_object source_obj, int count, string action);
    // workaround to array lookup in IUS?
    int _count = m_source_count.exists(obj) ? m_source_count[obj] : 0;
    int _total = m_total_count[obj];
    if (source_obj == obj)
      ovm_report_info("OBJTN_CNT", 
        $sformatf("Object %0s %0s %0d objection(s), count=%0d  total=%0d",
           obj.get_full_name()==""?"ovm_top":obj.get_full_name(), action, count, _count, _total), OVM_HIGH);
    else begin
      ovm_report_info("OBJTN_CNT",
        $sformatf("Object %0s %0s %0d objection(s) from its total (%s from source object %s), count=%0d  total=%0d",
           obj.get_full_name()==""?"ovm_top":obj.get_full_name(), action=="raised"?"added":"subtracted",
            count, action, source_obj.get_full_name(), _count, _total), OVM_HIGH);
    end
  endfunction


  // Function- m_get_parent
  //
  // Internal method for getting the parent of the given ~object~.
  // The ultimate parent is ovm_top, OVM's implicit top-level component. 

  function ovm_object m_get_parent(ovm_object obj);
    ovm_component comp;
    ovm_sequence_base seq;
    if ($cast(comp, obj)) begin
      obj = comp.get_parent();
    end
    else if ($cast(seq, obj)) begin
       obj = seq.get_sequencer();
    end
    else
      obj = top;
    if (obj == null)
      obj = top;
    return obj;
  endfunction


  // Function- m_propagate
  //
  // Propagate the objection to the objects parent. If the object is a
  // component, the parent is just the hierarchical parent. If the object is
  // a sequence, the parent is the parent sequence if one exists, or
  // it is the attached sequencer if there is no parent sequence. 
  //
  // obj : the ovm_object on which the objection is being raised or lowered
  // source_obj : the root object on which the end user raised/lowered the 
  //   objection (as opposed to an anscestor of the end user object)a
  // count : the number of objections associated with the action.
  // raise : indicator of whether the objection is being raised or lowered. A
  //   1 indicates the objection is being raised.

  function void m_propagate (ovm_object obj, ovm_object source_obj, int count, bit raise);
    if (obj != null && obj != top) begin
      obj = m_get_parent(obj);
      if(raise)
        m_raise(obj, source_obj, count);
      else
        m_drop(obj, source_obj, count);
    end
  endfunction


  // Group: Objection Control
  
  // Hierarchical mode only needs to be set for intermediate components, not
  // for ovm_root or a leaf component.
  function void m_set_hier_mode (ovm_object obj);
    ovm_component c;
    if((m_hier_mode == 1) || (obj == top)) begin
      // Don't set if already set or the object is ovm_top.
      return;
    end
    if($cast(c,obj)) begin
      // Don't set if object is a leaf.
      if(c.get_num_children() == 0) begin
        return;
      end
    end
    else begin
      // Don't set if object is a non-component.
      return;
    end

    // restore counts on non-source nodes
    m_total_count.delete();
    foreach (m_source_count[obj]) begin
      ovm_object theobj = obj;
      int count = m_source_count[obj];
      do begin
        if (m_total_count.exists(theobj))
          m_total_count[theobj] += count;
        else
          m_total_count[theobj] = count;
        theobj = m_get_parent(theobj);
      end
      while (theobj != null);
    end
    
    m_hier_mode = 1;
  endfunction

  // Function: raise_objection
  //
  // Raises the number of objections for the source ~object~ by ~count~, which
  // defaults to 1.  The ~object~ is usually the ~this~ handle of the caller.
  // If ~object~ is not specified or null, the implicit top-level component,
  // ~ovm_top~, is chosen.
  //
  // Rasing an objection causes the following.
  //
  // - The source and total objection counts for ~object~ are increased by
  //   ~count~.
  //
  // - The objection's <raised> virtual method is called, which calls the
  //   <ovm_component::raised> method for all of the components up the 
  //   hierarchy.
  //

  function void raise_objection (ovm_object obj=null, int count=1);
    if (obj == null)
      obj = top;
    m_raise (obj, obj, count);
  endfunction


  // Function- m_raise

  function void m_raise (ovm_object obj, ovm_object source_obj, int count=1);

    if (m_total_count.exists(obj))
      m_total_count[obj] += count;
    else 
      m_total_count[obj] = count;

    if (source_obj==obj) begin
      if (m_source_count.exists(obj))
        m_source_count[obj] += count;
      else
        m_source_count[obj] = count;
      source_obj = obj;
    end
  
    if (ovm_report_enabled(OVM_FULL,OVM_INFO,"OBJTN_CNT"))
      m_report(obj,source_obj,count,"raised");

    raised(obj, source_obj, count);

    // If this object is still draining from a previous drop, then
    // raise the count and return. Any propagation will be handled
    // by the drain process.
    if (m_draining.exists(obj))
      return;

    if (!m_hier_mode && obj != top)
      m_raise(top,source_obj,count);
    else if (obj != top)
      m_propagate(obj, source_obj, count, 1);
  
  endfunction
  

  // Function: drop_objection
  //
  // Drops the number of objections for the source ~object~ by ~count~, which
  // defaults to 1.  The ~object~ is usually the ~this~ handle of the caller.
  // If ~object~ is not specified or null, the implicit top-level component,
  // ~ovm_top~, is chosen.
  //
  // Dropping an objection causes the following.
  //
  // - The source and total objection counts for ~object~ are decreased by
  //   ~count~. It is an error to drop the objection count for ~object~ below
  //   zero.
  //
  // - The objection's <dropped> virtual method is called, which calls the
  //   <ovm_component::dropped> method for all of the components up the 
  //   hierarchy.
  //
  // - If the total objection count has not reached zero for ~object~, then
  //   the drop is propagated up the object hierarchy as with
  //   <raise_objection>. Then, each object in the hierarchy will have updated
  //   their ~source~ counts--objections that they originated--and ~total~
  //   counts--the total number of objections by them and all their
  //   descendants.
  //
  // If the total objection count reaches zero, propagation up the hierarchy
  // is deferred until a configurable drain-time has passed and the 
  // <ovm_component::all_dropped> callback for the current hierarchy level
  // has returned. The following process occurs for each instance up
  // the hierarchy from the source caller:
  //
  // A process is forked in a non-blocking fashion, allowing the ~drop~
  // call to return. The forked process then does the following:
  //
  // - If a drain time was set for the given ~object~, the process waits for
  //   that amount of time.
  //
  // - The objection's <all_dropped> virtual method is called, which calls the
  //   <ovm_component::all_dropped> method (if ~object~ is a component).
  //
  // - The process then waits for the ~all_dropped~ callback to complete.
  //
  // - After the drain time has elapsed and all_dropped callback has
  //   completed, propagation of the dropped objection to the parent proceeds
  //   as described in <raise_objection>, except as described below.
  //
  // If a new objection for this ~object~ or any of its descendents is raised
  // during the drain time or during execution of the all_dropped callback at
  // any point, the hierarchical chain described above is terminated and the
  // dropped callback does not go up the hierarchy. The raised objection will
  // propagate up the hierarchy, but the number of raised propagated up is
  // reduced by the number of drops that were pending waiting for the 
  // all_dropped/drain time completion. Thus, if exactly one objection
  // caused the count to go to zero, and during the drain exactly one new
  // objection comes in, no raises or drops are propagted up the hierarchy,
  //
  // As an optimization, if the ~object~ has no set drain-time and no
  // registered callbacks, the forked process can be skipped and propagation
  // proceeds immediately to the parent as described. 

  function void drop_objection (ovm_object obj=null, int count=1);
    if (obj == null)
      obj = top;
    m_drop (obj, obj, count);
  endfunction


  // Function- m_drop

  function void m_drop (ovm_object obj, ovm_object source_obj, int count=1);

    if (!m_total_count.exists(obj) || (count > m_total_count[obj])) begin
      ovm_report_fatal("OBJTN_ZERO", {"Object \"", obj.get_full_name(), 
        "\" attempted to drop objection count below zero."});
      return;
    end
    if ((obj == source_obj) && 
        (!m_source_count.exists(obj) || (count > m_source_count[obj]))) begin
      ovm_report_fatal("OBJTN_ZERO", {"Object \"", obj.get_full_name(), 
        "\" attempted to drop objection count below zero."});
      return;
    end

    m_total_count[obj] -= count;

    if (source_obj==obj) begin
      m_source_count[obj] -= count;
      source_obj = obj;
    end
  
    if (ovm_report_enabled(OVM_FULL,OVM_INFO,"OBJTN_CNT"))
      m_report(obj,source_obj,count,"dropped");
    
    dropped(obj, source_obj, count);
  
    // if count != 0, no reason to fork
    if (m_total_count[obj] != 0) begin

      if (!m_hier_mode && obj != top)
        m_drop(top,source_obj,count);
      else if (obj != top)
        this.m_propagate(obj, source_obj, count, 0);

    end
    else begin

        int diff_count;
        bit reraise;

        m_draining[obj] = 1;

        fork begin

         if (m_total_count[obj] == 0) begin
           fork begin //wrapper thread for disable fork
              fork
                begin
                  if (m_drain_time.exists(obj))
                    #(m_drain_time[obj]);

                  all_dropped(obj,source_obj,count);
  
                  // wait for all_dropped cbs to complete
                  wait fork;
                end
                wait (m_total_count[obj] != 0);
              join_any
              disable fork;
           end join
          end

          m_draining.delete(obj);

          diff_count = m_total_count[obj] - count;

          // no propagation if the re-raise cancels the drop
          if (diff_count != 0) begin
            reraise = diff_count > 0 ? 1 : 0;

            if (diff_count < 0)
              diff_count = -diff_count;

            if (!m_hier_mode && obj != top) begin
              if (reraise)
                m_raise(top,source_obj,diff_count);
              else
                m_drop(top,source_obj,diff_count);
            end
            else
              if (obj != top) begin
                this.m_propagate(obj, source_obj, diff_count, reraise);
              end
          end

        end
        join_none

    end

  endfunction


  // Function: set_drain_time
  //
  // Sets the drain time on the given ~object~ to ~drain~.
  //
  // The drain time is the amount of time to wait once all objections have
  // been dropped before calling the all_dropped callback and propagating
  // the objection to the parent. 
  //
  // If a new objection for this ~object~ or any of its descendents is raised
  // during the drain time or during execution of the all_dropped callbacks,
  // the drain_time/all_dropped execution is terminated. 

  function void set_drain_time (ovm_object obj, time drain);
    m_drain_time[obj] = drain;
    m_set_hier_mode(obj);
  endfunction
  

  // Group: Callback Hooks

  // Function: raised
  //
  // Objection callback that is called when a <raise_objection> has reached ~obj~.
  // The default implementation calls <ovm_component::raised>.

  virtual function void raised (ovm_object obj, ovm_object source_obj, int count);
    ovm_component comp;
    if ($cast(comp,obj))    
      comp.raised(this, source_obj, count);
  endfunction


  // Function: dropped
  //
  // Objection callback that is called when a <drop_objection> has reached ~obj~.
  // The default implementation calls <ovm_component::dropped>.

  virtual function void dropped (ovm_object obj, ovm_object source_obj, int count);
    ovm_component comp;
    if($cast(comp,obj))    
      comp.dropped(this, source_obj, count);
  endfunction


  // Function: all_dropped
  //
  // Objection callback that is called when a <drop_objection> has reached ~obj~,
  // and the total count for ~obj~ goes to zero. This callback is executed
  // after the drain time associated with ~obj~. The default implementation 
  // calls <ovm_component::all_dropped>.

  virtual task all_dropped (ovm_object obj, ovm_object source_obj, int count);
    ovm_component comp;
    if($cast(comp,obj))    
      comp.all_dropped(this, source_obj, count);
  endtask


  // Group: Objection Status

  // Function: get_objection_count
  //
  // Returns the current number of objections raised by the given ~object~.

  function int get_objection_count (ovm_object obj);
    if (!m_source_count.exists(obj))
      return 0;
    return m_source_count[obj];
  endfunction
  

  // Function: get_objection_total
  //
  // Returns the current number of objections raised by the given ~object~ 
  // and all descendants.

  function int get_objection_total (ovm_object obj=null);
    ovm_component c;
    string ch;
 
    if (obj==null)
      obj = top;

    if (!m_total_count.exists(obj))
      return 0;
    if (m_hier_mode) 
      return m_total_count[obj];
    else begin
      if ($cast(c,obj)) begin
        get_objection_total = m_source_count[obj];
        if (c.get_first_child(ch))
        do
          get_objection_total += get_objection_total(c.get_child(ch));
        while (c.get_next_child(ch));
      end
      else begin
        return m_total_count[obj];
      end
    end
  endfunction
  

  // Function: get_drain_time
  //
  // Returns the current drain time set for the given ~object~ (default: 0 ns).

  function time get_drain_time (ovm_object obj);
    if (!m_drain_time.exists(obj))
      return 0;
    return m_drain_time[obj];
  endfunction


  // Function: display_objections
  // 
  // Displays objection information about the given ~object~. If ~object~ is
  // not specified or ~null~, the implicit top-level component, <ovm_top>, is
  // chosen. The ~show_header~ argument allows control of whether a header is
  // output.

  protected function string m_display_objections(ovm_object obj=null, bit show_header=1);

    static string blank="                                                                                   ";
    
    string s;
    int total;
    ovm_object list[string];
    ovm_object curr_obj;
    int depth;
    string name;
    string this_obj_name;
    string curr_obj_name;
  
    foreach (m_total_count[o]) begin
      ovm_object theobj = o; 
      if ( m_total_count[o] > 0)
        list[theobj.get_full_name()] = theobj;
    end

    if (obj==null)
      obj = top;

    total = get_objection_total(obj);
    
    s = $sformatf("The total objection count is %0d\n",total);

    if (total == 0)
      return s;

    s = {s,"---------------------------------------------------------\n"};
    s = {s,"Source  Total   \n"};
    s = {s,"Count   Count   Object\n"};
    s = {s,"---------------------------------------------------------\n"};

  
    this_obj_name = obj.get_full_name();
    curr_obj_name = this_obj_name;

    do begin

      curr_obj = list[curr_obj_name];
  
      // determine depth
      depth=0;
      foreach (curr_obj_name[i])
        if (curr_obj_name[i] == ".")
          depth++;

      // determine leaf name
      name = curr_obj_name;
      for (int i=curr_obj_name.len()-1;i >= 0; i--)
        if (curr_obj_name[i] == ".") begin
           name = curr_obj_name.substr(i+1,curr_obj_name.len()-1); 
           break;
        end
      if (curr_obj_name == "")
        name = "ovm_top";
      else
        depth++;

      // print it
      s = {s, $sformatf("%-6d  %-6d %s%s\n",
         m_source_count.exists(curr_obj) ? m_source_count[curr_obj] : 0,
         m_total_count.exists(curr_obj) ? m_total_count[curr_obj] : 0,
         blank.substr(0,2*depth), name)};

    end while (list.next(curr_obj_name) &&
        curr_obj_name.substr(0,this_obj_name.len()-1) == this_obj_name);
  
    s = {s,"---------------------------------------------------------\n"};

    return s;

  endfunction
  

  function string convert2string();
    return m_display_objections(top,1);
  endfunction
    
  function void display_objections(ovm_object obj=null, bit show_header=1);
    $display(m_display_objections(obj,show_header));
  endfunction


  // Below is all of the basic data stuff that is needed for an ovm_object
  // for factory registration, printing, comparing, etc.

  typedef ovm_object_registry#(ovm_objection,"ovm_objection") type_id;
  static function type_id get_type();
    return type_id::get();
  endfunction

  function ovm_object create (string name="");
    ovm_objection tmp = new(name);
    return tmp;
  endfunction

  virtual function string get_type_name ();
    return "ovm_objection";
  endfunction

  function void do_copy (ovm_object rhs);
    ovm_objection _rhs;
    $cast(_rhs, rhs);
    m_source_count = _rhs.m_source_count;
    m_total_count  = _rhs.m_total_count;
    m_drain_time   = _rhs.m_drain_time;
    m_draining     = _rhs.m_draining;
    m_hier_mode    = _rhs.m_hier_mode;
  endfunction

endclass



//------------------------------------------------------------------------------
//
// Class: ovm_test_done_objection
//
// Built-in end-of-test coordination
//------------------------------------------------------------------------------

class ovm_test_done_objection extends ovm_objection;

  protected static ovm_test_done_objection m_inst = null;
  protected bit m_forced;

//  local function new();
  function new(string name="ovm_test_done");
    super.new(name);
  endfunction

  // Function: qualify
  //
  // Checks that the given ~object~ is derived from either <ovm_component> or
  // <ovm_sequence_base>.

  virtual function void qualify(ovm_object obj=null, bit is_raise);
    ovm_component c;
    ovm_sequence_base s;
    string nm = is_raise ? "raise_objection" : "drop_objection";
    if(! ($cast(c,obj) || $cast(s,obj))) begin
      ovm_report_error("TEST_DONE_NOHIER", {"A non-hierarchical object, '",
        obj.get_full_name(), "' (", obj.get_type_name(),") was used in a call ",
        "to ovm_test_done.", nm,"(). For this objection, a sequence ",
        "or component is required." });
    end
  endfunction


  // Task: all_dropped
  //
  // This callback is called when the given ~object's~ objection count reaches
  // zero; if the ~object~ is the implicit top-level, <ovm_top> then it means
  // there are no more objections raised for the ~ovm_test_done~ objection.
  // Thus, after calling <ovm_objection::all_dropped>, this method will call
  // <global_stop_request> to stop the current task-based phase (e.g. run).
  
  virtual task all_dropped (ovm_object obj, ovm_object source_obj, int count);
    super.all_dropped(obj,source_obj,count);
    if (obj == top) begin
      string msg = "", msg2 = "";
      if (!m_forced)
        msg = "All end_of_test objections have been dropped. ";
      if (!top.m_in_stop_request) begin
        msg = {msg, "Calling global_stop_request()"};
        top.stop_request();
      end
      else
        msg = {msg, "Previous call to global_stop_request() will now be honored."};
      ovm_report_info("TEST_DONE", msg, OVM_LOW);
    end
  endtask


  // Function: raise_objection
  //
  // Calls <ovm_objection::raise_objection> after calling <qualify>. 
  // If the ~object~ is not provided or is ~null~, then the implicit top-level
  // component, ~ovm_top~, is chosen.

  virtual function void raise_objection (ovm_object obj=null, int count=1);
    if(obj==null)
      obj=top;
    else
      qualify(obj, 1);
    super.raise_objection(obj,count);
  endfunction


  // Function: drop
  //
  // Calls <ovm_objection::drop_objection> after calling <qualify>. 
  // If the ~object~ is not provided or is ~null~, then the implicit top-level
  // component, ~ovm_top~, is chosen.

  virtual function void drop_objection (ovm_object obj=null, int count=1);
    if(obj==null)
      obj=top;
    else
      qualify(obj, 0);
    super.drop_objection(obj,count);
  endfunction


  // Function: force_stop
  //
  // 
  virtual task force_stop(ovm_object obj=null);
    string name;
    if (obj==null)
      obj=top;
    name = obj.get_full_name();
    if (name == "")
      name = "ovm_top";
    m_forced = 1;
    ovm_report_warning("FORCE_STOP",{"Object '",name,"' called force_stop. ",
       "Ending run phase"});
    all_dropped(ovm_top, obj, 0);
    m_forced = 0;
  endtask

  // Below is all of the basic data stuff that is needed for an ovm_object
  // for factory registration, printing, comparing, etc.

  typedef ovm_object_registry#(ovm_test_done_objection,"ovm_test_done") type_id;
  static function type_id get_type();
    return type_id::get();
  endfunction

  function ovm_object create (string name="");
    ovm_test_done_objection tmp = new(name);
    return tmp;
  endfunction

  virtual function string get_type_name ();
    return "ovm_test_done";
  endfunction

  static function ovm_test_done_objection get();
    if(m_inst == null)
      m_inst = ovm_test_done_objection::type_id::create("ovm_test_done");
    return m_inst;
  endfunction

endclass


`endif

