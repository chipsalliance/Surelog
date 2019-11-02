// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_phases.sv#25 $
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

`ifndef OVM_PHASES_SVH
`define OVM_PHASES_SVH

typedef class ovm_component;

//------------------------------------------------------------------------------
//
// Class: ovm_phase
//
// The ovm_phase class is used for defining phases for ovm_component and its
// subclasses.  For a list of predefined phases see
// <ovm_component::Phasing Interface>
//
//------------------------------------------------------------------------------

virtual class ovm_phase;

  local  string  m_name;
  local  bit     m_is_top_down;
  local  bit     m_is_task;

  local  event   m_start_event;
  local  bit     m_is_started=0;
  local  event   m_done_event;
  local  bit     m_is_done=0;
  local  bit     m_executed[int];

  local  ovm_phase m_aliases[$];
  local  ovm_phase m_insertion_phase;

  // Function: new
  //
  // Creates a phase object. 
  //
  // The name is the name of the phase. When is_top_down is set, the parent is
  // phased before its children. is_task indicates whether the phase callback is
  // a task (1) or function (0). Only tasks may consume simulation time and
  // execute blocking statements.

  function new (string name, bit is_top_down, bit is_task);
    m_name = name;
    m_is_top_down = is_top_down;
    m_is_task     = is_task;
  endfunction


  //----------------//
  // Info interface //
  //----------------//

  // Function: get_name
  //
  // Returns the name of the phase object as supplied in the constructor.

  function string get_name       (); return m_name;        endfunction


  // Function: is_task
  //
  // Returns 1 if the phase is time consuming and 0 if not.

  function bit    is_task        (); return m_is_task;     endfunction


  // Function: is_top_down
  //
  // Returns 1 if the phase executes top-down (executes the parent¿s phase
  // callback before executing the children¿s callback) and 0 otherwise.

  function bit    is_top_down    (); return m_is_top_down; endfunction

  // Function: get_type_name
  //
  // Derived classes should override this method to return the phase type name.

  virtual function string get_type_name();
    return "ovm_phase";
  endfunction

  //--------------------------//
  // Event & Status interface //
  //--------------------------//

  // Task: wait_start
  //
  // Waits until the phase has beed started.

  task wait_start ();
    @m_start_event;
  endtask


  // Task: wait_done
  //
  // Waits until the phase has been completed.

  task wait_done ();
    @m_done_event;
  endtask


  // Function: is_in_progress
  //
  // Returns 1 if the phase is currently in progress (active), 0 otherwise.

  function bit is_in_progress ();
    return m_is_started;
  endfunction


  // Function: is_done
  //
  // Returns 1 if the phase has completed, 0 otherwise.

  function bit is_done ();
    return m_is_done;
  endfunction


  // Function: reset
  //
  // Resets phase state such that is_done and is_in_progress both return 0.

  function void  reset ();
    m_is_done=0;
    m_is_started=0;       
    m_executed.delete();
    foreach(m_aliases[i]) 
      m_aliases[i].reset();
  endfunction


  // Task: call_task
  //
  // Calls the task-based phase of the component given by parent, which must be
  // derived from ovm_component. A task-based phase is defined by subtyping
  // ovm_phase and overriding this method. The override must $cast the base
  // parent handle to the actual component type that defines the phase callback,
  // and then call the phase callback.

  virtual task call_task (ovm_component parent);
     foreach(m_aliases[i]) m_aliases[i].call_task(parent);
     return;
  endtask


  // Function: call_func
  //
  // Calls the function-based phase of the component given by parent. A
  // function-based phase is defined by subtyping ovm_phase and overriding this
  // method. The override must $cast the base parent handle to the actual
  // component type that defines the phase callback, and then call that
  // phase callback.

  virtual function void call_func (ovm_component parent);
     foreach(m_aliases[i]) m_aliases[i].call_func(parent);
    return;
  endfunction

  // psuedo-private methods; do not call directly

  function void m_set_is_started(bit val);
    foreach(m_aliases[i]) m_aliases[i].m_set_is_started(val);
    m_is_started=val;
  endfunction

  function void m_set_in_progress();
    foreach(m_aliases[i]) m_aliases[i].m_set_in_progress();
    m_set_is_started(1);
    ->m_start_event;
  endfunction

  function void m_set_done();
    foreach(m_aliases[i]) m_aliases[i].m_set_done();
    m_is_done=1;
    m_set_is_started(0);
    ->m_done_event;
  endfunction

  function void set_insertion_phase(ovm_phase phase);
    if(m_insertion_phase != null) begin
      ovm_report_warning("INSPHS", "Cannot set the insertion phase for a phase that has already been set");
      return;
    end
    m_insertion_phase = phase;
  endfunction

  function ovm_phase get_insertion_phase();
    return m_insertion_phase;
  endfunction

  function bit has_executed(ovm_component comp);
    if(m_executed.exists(comp.get_inst_id())) return 1;
    foreach(m_aliases[i])
      if(m_aliases[i].has_executed(comp)) return 1;
    return 0;
  endfunction

  function void set_executed(ovm_component comp);
    m_executed[comp.get_inst_id()] = 1;
  endfunction

  function void add_alias(ovm_phase the_alias, exist_ph);
    ovm_phase insertion_phase;
    string    alias_nm, insrt_nm, alias_insrt_nm;
    //if the alias is null then return
    if(the_alias == null) return;
    if(the_alias == this && m_insertion_phase == exist_ph) return;

    alias_nm = the_alias.get_name();

    //This warning can't happen from ovm_root, but in theory a user could create
    //their own phase controller in which case, aliasing different names is probably
    //not desireable.
    if(alias_nm != get_name()) begin
      ovm_report_warning("PHSALS", {
        "Phases ", get_name(), " and ", alias_nm, 
        " are being aliased, but have different phase names"});
    end

    //verify that the aliased phase has the same semantics as the
    //master phase.
    if(m_is_task != the_alias.is_task()) begin
      ovm_report_fatal("PHSALS", {
        "Phases ", get_name(), " and ", alias_nm, 
        " are being aliased, but one is a function phase and one is a task phase"}, OVM_NONE);
      return;
    end
    if(m_is_top_down != the_alias.is_top_down()) begin
      ovm_report_fatal("PHSALS", {
        "Phases ", get_name(), " and ", alias_nm, 
        " are being aliased, but one is top-down and the other is bottom-up"}, OVM_NONE);
      return;
    end
    if(exist_ph != null)
       alias_insrt_nm = exist_ph.get_name();
    else
       alias_insrt_nm = "the topmost phase";
    if(m_insertion_phase != null)
       insrt_nm = m_insertion_phase.get_name();
    else
       insrt_nm = "the topmost phase";
    if(insrt_nm != alias_insrt_nm) begin
      ovm_report_fatal("PHSALS", {
        "Phases ", get_name(), " and ", alias_nm, 
        " are being aliased, they have different insertion phase, \"",
        insrt_nm, "\" versus \"", alias_insrt_nm, "\""}, OVM_NONE); 
      return;
    end

    //for existing aliases, we needed to verify the insertion phase
    //which is why we wait to the end before we exit.
    foreach(m_aliases[i]) if (the_alias == m_aliases[i]) return;
    if(the_alias == this) return;

    the_alias.set_insertion_phase(exist_ph);
    m_aliases.push_back(the_alias);
  endfunction
endclass


// Section: Usage
//
// Phases are a synchronizing mechanism for the environment. They are
// represented by callback methods. A set of predefined phases and corresponding
// callbacks are provided in ovm_component. Any class deriving from
// ovm_component may implement any or all of these callbacks, which are executed
// in a particular order. Depending on the properties of any given phase, the
// corresponding callback is either a function or task, and it is executed in
// top-down or bottom-up order.
//
// The OVM provides the following predefined phases for all ovm_components.
//
//   build     - Depending on configuration and factory settings,
//             create and configure additional component hierarchies.
//
//   connect   - Connect ports, exports, and implementations (imps).
//
//   end_of_elaboration - Perform final configuration, topology, connection,
//             and other integrity checks.
//
//   start_of_simulation - Do pre-run activities such as printing banners,
//             pre-loading memories, etc.
//
//   run       - Most verification is done in this time-consuming phase. May fork
//             other processes. Phase ends when global_stop_request is called
//             explicitly.
//
//   extract   - Collect information from the run in preparation for checking.
//
//   check     - Check simulation results against expected outcome.
//
//   report    - Report simulation results.
//
// A phase is defined by an instance of an ~ovm_phase~ subtype. If a phase is to
// be shared among several component types, the instance must be accessible from
// a common scope, such as a package.
// 
// To have a user-defined phase get called back during simulation, the phase
// object must be registered with the top-level OVM phase controller, ovm_top. 
//
// Inheriting from the ~ovm_phase~ Class:
//
// When creating a user-defined phase, you must do the following.
//
// 1.  Define a new phase class, which must extend ~ovm_phase~. To enable use of
//     the phase by any component, we recommend this class be parameterized.
//     The easiest way to define a new phase is to invoke a predefined macro.
//     For example:
//
//     | `ovm_phase_func_topdown_decl( preload )
//
//    This convenient phase declaration macro is described below.
//
// 2.  Create a single instance of the phase in a convenient placein a package,
//     or in the same scope as the component classes that will use the phase.
//
//     | typedef class my_memory;
//     | preload_phase #(my_memory) preload_ph = new;
//
// 3.  Register the phase object with ovm_top. 
//
//     | class my_memory extends ovm_component;
//     |   function new(string name, ovm_component parent);
//     |     super.new(name,parent);
//     |     ovm_top.insert_phase(preload_ph, start_of_simulation_ph);
//     |   endfunction
//     |   virtual function void preload(); // our new phase
//     |     ...
//     |   endfunction
//     | endclass
//
//
// Phase Macros (Optional):
// 
// The following macros simplify the process of creating a user-defined phase. They
// create a phase type that is parameterized to the component class that uses the
// phase.
// 
// Macro: `ovm_phase_func_decl
//
// `ovm_phase_func_decl (PHASE_NAME, TOP_DOWN)
//
// The ~PHASE_NAME~ argument is used to define the name of the phase, the name of
// the component method that is called back during phase execution, and the
// prefix of the type-name of the phase class that gets generated.
// 
// The above macro creates the following class definition. 
// 
//|  class PHASE_NAME``_phase #(type PARENT=int) extends ovm_phase;
//|
//|    PARENT m_parent;
//|
//|    function new();
//|       super.new(`"NAME`",TOP_DOWN,1);
//|    endfunction
//|    virtual function void call_func();
//|       m_parent.NAME(); // call the component¿s phase callback
//|    endtask
//|    virtual task execute(ovm_component parent);
//|       assert($cast(m_parent,parent));
//|       call_func();
//|    endtask
//|  endclass
// 
// Macro: `ovm_phase_task_decl
//
//| `ovm_phase_task_decl (PHASE_NAME, TOP_DOWN)
// 
// The above macro creates the following class definition.
// 
//|  class PHASE_NAME``_phase #(type PARENT=int) extends ovm_phase;
//|    PARENT m_parent;
//|    function new();
//|     super.new(`"NAME`",TOP_DOWN,1);
//|    endfunction
//|    virtual task call_task();
//|         m_parent.NAME(); // call the component¿s phase callback
//|    endtask
//|    virtual task execute(ovm_component parent);
//|         assert($cast(m_parent,parent));
//|         call_task();
//|    endtask
//|  endclass
// 
//
// Macro: `ovm_phase_func_topdown_decl
//
// Macro: `ovm_phase_func_bottomup_decl
//
// Macro: `ovm_phase_task_topdown_decl
//
// Macro: `ovm_phase_task_bottomup_decl
// 
// These alternative macros have a single phase name argument. The top-down or
// bottom-up selection is specified in the macro name, which makes them more
// self-documenting than those with a 0 or 1 2nd argument.
//
//|  `define ovm_phase_func_topdown_decl  `ovm_phase_func_decl (PHASE_NAME,1)
//|  `define ovm_phase_func_bottomup_decl `ovm_phase_func_decl (PHASE_NAME,0)
//|  `define ovm_phase_task_topdown_decl  `ovm_phase_task_decl (PHASE_NAME,1)
//|  `define ovm_phase_task_bottomup_decl `ovm_phase_task_decl (PHASE_NAME,0)
// 

`endif // OVM_PHASES_SVH
