// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_component.svh#56 $
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

`ifndef OVM_COMPONENT_SVH
`define OVM_COMPONENT_SVH

typedef class ovm_objection;

`include "base/ovm_config.svh"

//------------------------------------------------------------------------------
//
// CLASS: ovm_component
//
// The ovm_component class is the root base class for OVM components. In
// addition to the features inherited from <ovm_object> and <ovm_report_object>,
// ovm_component provides the following interfaces:
//
// Hierarchy - provides methods for searching and traversing the component
//     hierarchy.
//
// Configuration - provides methods for configuring component topology and other
//     parameters ahead of and during component construction.
//
// Phasing - defines a phased test flow that all components follow. Derived
//     components implement one or more of the predefined phase callback methods
//     to perform their function. During simulation, all components' callbacks
//     are executed in precise order. Phasing is controlled by ovm_top, the
//     singleton instance of <ovm_root>.
//
// Reporting - provides a convenience interface to the <ovm_report_handler>. All
//     messages, warnings, and errors are processed through this interface.
//
// Transaction recording - provides methods for recording the transactions
//     produced or consumed by the component to a transaction database (vendor
//     specific). 
//
// Factory - provides a convenience interface to the <ovm_factory>. The factory
//     is used to create new components and other objects based on type-wide and
//     instance-specific configuration.
//
// The ovm_component is automatically seeded during construction using OVM
// seeding, if enabled. All other objects must be manually reseeded, if
// appropriate. See <ovm_object::reseed> for more information.
//
//------------------------------------------------------------------------------

virtual class ovm_component extends ovm_report_object;

  // Function: new
  //
  // Creates a new component with the given leaf instance ~name~ and handle to
  // to its ~parent~.  If the component is a top-level component (i.e. it is
  // created in a static module or interface), ~parent~ should be null.
  //
  // The component will be inserted as a child of the ~parent~ object, if any.
  // If ~parent~ already has a child by the given ~name~, an error is produced.
  //
  // If ~parent~ is null, then the component will become a child of the
  // implicit top-level component, ~ovm_top~.
  //
  // All classes derived from ovm_component must call super.new(name,parent).

  extern function new (string name, ovm_component parent);


  //----------------------------------------------------------------------------
  // Group: Hierarchy Interface
  //----------------------------------------------------------------------------
  //
  // These methods provide user access to information about the component
  // hierarchy, i.e., topology.
  // 
  //----------------------------------------------------------------------------

  // Function: get_parent
  //
  // Returns a handle to this component's parent, or null if it has no parent.

  extern virtual function ovm_component get_parent ();


  // Function: get_full_name
  //
  // Returns the full hierarchical name of this object. The default
  // implementation concatenates the hierarchical name of the parent, if any,
  // with the leaf name of this object, as given by <ovm_object::get_name>. 

  extern virtual function string get_full_name ();


  // Function: get_child
  extern function ovm_component get_child (string name);

  // Function: get_next_child
  extern function int get_next_child (ref string name);

  // Function: get_first_child
  //
  // These methods are used to iterate through this component's children, if
  // any. For example, given a component with an object handle, ~comp~, the
  // following code calls <ovm_object::print> for each child:
  //
  //|    string name;
  //|    ovm_component child;
  //|    if (comp.get_first_child(name))
  //|      do begin
  //|        child = comp.get_child(name);
  //|        child.print();
  //|      end while (comp.get_next_child(name));

  extern function int get_first_child (ref string name);


  // Function: get_num_children
  //
  // Returns the number of this component's children. 

  extern function int get_num_children ();


  // Function: has_child
  //
  // Returns 1 if this component has a child with the given ~name~, 0 otherwise.

  extern function int has_child (string name);


  // Function: set_name
  //
  // Renames this component to ~name~ and recalculates all descendants'
  // full names.

  extern virtual function void set_name (string name);

  
  // Function: lookup
  //
  // Looks for a component with the given hierarchical ~name~ relative to this
  // component. If the given ~name~ is preceded with a '.' (dot), then the search
  // begins relative to the top level (absolute lookup). The handle of the
  // matching component is returned, else null. The name must not contain
  // wildcards.

  extern function ovm_component lookup (string name);



  //----------------------------------------------------------------------------
  // Group: Phasing Interface
  //----------------------------------------------------------------------------
  // Components execute their behavior in strictly ordered, pre-defined phases.
  // Each phase is defined by its own method, which derived components can
  // override to incorporate component-specific behavior. During simulation,
  // the phases are executed one by one, where one phase must complete before
  // the next phase begins. The following briefly describe each phase:
  //
  // new - Also known as the ~constructor~, the component does basic
  //     initialization of any members not subject to configuration.
  //
  // build - The component constructs its children. It uses the get_config
  //     interface to obtain any configuration for itself, the set_config
  //     interface to set any configuration for its own children, and the
  //     factory interface for actually creating the children and other
  //     objects it might need.
  // 
  // connect - The component now makes connections (binds TLM ports and
  //     exports) from child-to-child or from child-to-self (i.e. to promote a
  //     child port or export up the hierarchy for external access. Afterward,
  //     all connections are checked via <resolve_bindings> before entering
  //     the <end_of_elaboration> phase. 
  //
  // end_of_elaboration - At this point, the entire testbench environment has
  //     been built and connected. No new components and connections may be
  //     created from this point forward. Components can do final checks for
  //     proper connectivity, and it can initiate communication with other tools
  //     that require stable, quasi-static component structure..
  //
  // start_of_simulation - The simulation is about to begin, and this phase
  //     can be used to perform any pre-run activity such as displaying banners,
  //     printing final testbench topology and configuration information.
  //
  // run - This is where verification takes place. It is the only predefined,
  //     time-consuming phase. A component's primary function is implemented
  //     in the <run> task. Other processes may be forked if desired. When
  //     a component returns from its run task, it does not signify completion
  //     of its run phase. Any processes that it may have forked ~continue to
  //     run~. The run phase terminates in one of four ways:
  //
  //     stop - When a component's <enable_stop_interrupt> bit is set and
  //            <global_stop_request> is called, the component's <stop> task
  //            is called. Components can implement stop to allow completion
  //            of in-progress transactions, <flush> queues, etc. Upon return
  //            from stop() by all enabled components, a <do_kill_all> is
  //            issued. If the <ovm_test_done_objection> is being used,
  //            this stopping procedure is deferred until all outstanding
  //            objections on <ovm_test_done> have been dropped.
  //
  //     objections dropped - The <ovm_test_done_objection> will implicitly
  //            call <global_stop_request> when all objections to ending the
  //            phase are dropped. The stop procedure described above is
  //            then allowed to proceed normally.
  //
  //     kill - When called, all component's <run> processes are killed
  //            immediately. While kill can be called directly, it is
  //            recommended that components use the stopping mechanism,
  //            which affords a more ordered and safe shut-down.
  //
  //     timeout - If a timeout was set, then the phase ends if it expires
  //            before either of the above occur. Without a stop, kill, or
  //            timeout, simulation can continue "forever", or the simulator
  //            may end simulation prematurely if it determines that
  //            all processes are waiting.
  //
  // extract - This phase can be used to extract simulation results from
  //     coverage collectors and scoreboards, collect status/error counts,
  //     statistics, and other information from components in bottom-up order.
  //     Being a separate phase, extract ensures all relevant data from
  //     potentially independent sources (i.e. other components) are collected
  //     before being checked in the next phase.
  //
  // check - Having extracted vital simulation results in the previous phase,
  //     the check phase can be used to validate such data and determine
  //     the overall simulation outcome. It too executes bottom-up.
  //
  // report - Finally, the report phase is used to output results to files
  //     and/or the screen. 
  //
  // All task-based phases (<run> is the only pre-defined task phase) will run
  // forever until killed or stopped via <kill> or <global_stop_request>.
  // The latter causes each component's <stop> task to get called back if
  // its <enable_stop_interrupt> bit is set. After all components' stop tasks
  // return, the OVM will end the phase.
  //
  // Note- the post_new, export_connections, import_connections, configure,
  // and pre_run phases are deprecated. <build> replaces post_new, <connect>
  // replaces both import_ and export_connections, and <start_of_simulation>
  // replaces pre_run.
  //
  //----------------------------------------------------------------------------

  // Function: build
  //
  // The build phase callback is the first of several methods automatically
  // called during the course of simulation. The build phase is the second of
  // a two-pass construction process (the first is the built-in new method).
  //
  // The build phase can add additional hierarchy based on configuration
  // information not available at time of initial construction. 
  // Any override should call super.build().
  //
  // Starting after the initial construction phase (<new> method) has completed,
  // the build phase consists of calling all components' build methods
  // recursively top-down, i.e., parents' build are executed before the
  // children. This is the only phase that executes top-down.
  //
  // The build phase of the ovm_component class executes the automatic
  // configuration of fields registed in the component by calling 
  // <apply_config_settings>.  To turn off automatic configuration for a component, 
  // do not call super.build() in the subtype's build method.
  //
  // See <ovm_phase> for more information on phases.

  extern virtual function void build ();


  // Function: connect
  //
  // The connect phase callback is one of several methods automatically called
  // during the course of simulation.
  //
  // Starting after the <build> phase has completed, the connect phase consists
  // of calling all components' connect methods recursively in depth-first,
  // bottom-up order, i.e., children are executed before their parents.
  //
  // Generally, derived classes should override this method to make port and
  // export connections via the similarly-named <ovm_port_base #(IF)::connect>
  // method. Any override should call super.connect().
  //
  // This method should never be called directly. 
  //
  // See <ovm_phase> for more information on phases.

  extern virtual function void connect ();


  // Function: end_of_elaboration
  //
  // The end_of_elaboration phase callback is one of several methods
  // automatically called during the course of simulation.
  //
  // Starting after the <connect> phase has completed, this phase consists of
  // calling all components' end_of_elaboration methods recursively in
  // depth-first, bottom-up order, i.e., children are executed before their
  // parents. 
  //
  // Generally, derived classes should override this method to perform any
  // checks on the elaborated hierarchy before the simulation phases begin.
  // Any override should call super.end_of_elaboration().
  //
  // This method should never be called directly.
  //
  // See <ovm_phase> for more information on phases.

  extern virtual function void end_of_elaboration ();


  // Function: start_of_simulation
  //
  // The start_of_simulation phase callback is one of several methods
  // automatically called during the course of simulation.
  //
  // Starting after the <end_of_elaboration> phase has completed, this phase
  // consists of calling all components' start_of_simulation methods recursively
  // in depth-first, bottom-up order, i.e. children are executed before their
  // parents. 
  //
  // Generally, derived classes should override this method to perform component-
  // specific pre-run operations, such as discovery of the elaborated hierarchy,
  // printing banners, etc. Any override should call super.start_of_simulation().
  //
  // This method should never be called directly.
  //
  // See <ovm_phase> for more information on phases.

  extern virtual function void start_of_simulation ();


  // Task: run
  //
  // The run phase callback is the only predefined phase that is time-consuming,
  // i.e., task-based. It executes after the <start_of_simulation> phase has
  // completed. Derived classes should override this method to perform the bulk
  // of its functionality, forking additional processes if needed.
  //
  // In the run phase, all components' run tasks are forked as independent
  // processes.  Returning from its run task does not signify completion of a
  // component's run phase; any processes forked by run continue to run.
  //
  // The run phase terminates in one of four ways.
  //
  // 1 - explicit call to <global_stop_request> - 
  //   When <global_stop_request> is called, an ordered shut-down for the
  //   currently running phase begins. First, all enabled components' status
  //   tasks are called bottom-up, i.e., childrens' <stop> tasks are called before
  //   the parent's. A component is enabled by its enable_stop_interrupt bit.
  //   Each component can implement stop to allow completion of in-progress
  //   transactions, flush queues, and other shut-down activities. Upon return
  //   from stop by all enabled components, the recursive do_kill_all is called
  //   on all top-level component(s).  If the <ovm_test_done> objection> is being
  //   used, this stopping procedure is deferred until all outstanding objections
  //   on <ovm_test_done> have been dropped.
  //
  // 2 - all objections to <ovm_test_done> have been dropped -
  //   When all objections on the <ovm_test_done> objection have been dropped,
  //   <global_stop_request> is called automatically, thus kicking off the
  //   stopping procedure described above. See <ovm_objection> for details on
  //   using the objection mechanism.
  //
  // 3 - explicit call to <kill> or <do_kill_all> -
  //   When <kill> is called, this component's run processes are killed immediately.
  //   The <do_kill_all> methods applies to this component and all its
  //   descendants. Use of this method is not recommended. It is better to use
  //   the stopping mechanism, which affords a more ordered, safer shut-down.
  //
  // 4 - timeout -
  //   The phase ends if the timeout expires before an explicit call to
  //   <global_stop_request> or kill. By default, the timeout is set to near the
  //   maximum simulation time possible. You may override this via
  //   <set_global_timeout>, but you cannot disable the timeout completely.
  //
  //   If the default timeout occurs in your simulation, or if simulation never
  //   ends despite completion of your test stimulus, then it usually indicates
  //   a missing call to <global_stop_request>.
  //
  // The run task should never be called directly.
  //
  // See <ovm_phase> for more information on phases.

  extern virtual task run ();


  // Function: extract
  //
  // The extract phase callback is one of several methods automatically called
  // during the course of simulation. 
  //
  // Starting after the <run> phase has completed, the extract phase consists of
  // calling all components' extract methods recursively in depth-first,
  // bottom-up order, i.e., children are executed before their parents. 
  //
  // Generally, derived classes should override this method to collect
  // information for the subsequent <check> phase when such information needs to
  // be collected in a hierarchical, bottom-up manner. Any override should
  // call super.extract().
  //
  // This method should never be called directly.
  //
  // See <ovm_phase> for more information on phases.

  extern virtual function void extract ();


  // Function: check
  //
  // The check phase callback is one of several methods automatically called
  // during the course of simulation.
  //
  // Starting after the <extract> phase has completed, the check phase consists of
  // calling all components' check methods recursively in depth-first, bottom-up
  // order, i.e., children are executed before their parents. 
  //
  // Generally, derived classes should override this method to perform component
  // specific, end-of-test checks. Any override should call super.check().
  //
  // This method should never be called directly.
  //
  // See <ovm_phase> for more information on phases.

  extern virtual function void check ();


  // Function: report
  //
  // The report phase callback is the last of several predefined phase
  // methods automatically called during the course of simulation.
  //
  // Starting after the <check> phase has completed, the report phase consists
  // of calling all components' report methods recursively in depth-first,
  // bottom-up order, i.e., children are executed before their parents. 
  //
  // Generally, derived classes should override this method to perform
  // component-specific reporting of test results. Any override should
  // call super.report().
  //
  // This method should never be called directly.
  //
  // See <ovm_phase> for more information on phases.

  extern virtual function void report ();


  // Task: suspend
  //
  // Suspends the process tree spawned from this component's currently
  // executing task-based phase, e.g. <run>.

  extern virtual task suspend ();


  // Task: resume
  //
  // Resumes the process tree spawned from this component's currently
  // executing task-based phase, e.g. <run>.

  extern virtual task resume ();


  // Function: status
  //
  // Returns the status of the parent process associated with the currently
  // running task-based phase, e.g., <run>.

  extern function string status ();

 
  // Function: kill
  //
  // Kills the process tree associated with this component's currently running
  // task-based phase, e.g., <run>.
  //
  // An alternative mechanism for stopping the <run> phase is the stop request.
  // Calling <global_stop_request> causes all components' run processes to be
  // killed, but only after all components have had the opportunity to complete
  // in progress transactions and shutdown cleanly via their <stop> tasks.

  extern virtual function void kill ();


  // Function: do_kill_all
  //
  // Recursively calls <kill> on this component and all its descendants,
  // which abruptly ends the currently running task-based phase, e.g., <run>.
  // See <run> for better options to ending a task-based phase.

  extern virtual  function void  do_kill_all ();


  // Task: stop
  //
  // The stop task is called when this component's <enable_stop_interrupt> bit
  // is set and <global_stop_request> is called during a task-based phase,
  // e.g., <run>.
  //
  // Before a phase is abruptly ended, e.g., when a test deems the simulation
  // complete, some components may need extra time to shut down cleanly. Such
  // components may implement stop to finish the currently executing
  // transaction, flush the queue, or perform other cleanup. Upon return from
  // its stop, a component signals it is ready to be stopped. 
  //
  // The stop method will not be called if <enable_stop_interrupt> is 0.
  //
  // The default implementation of stop is empty, i.e., it will return immediately.
  //
  // This method should never be called directly.

  extern virtual task stop (string ph_name);


  // Variable: enable_stop_interrupt
  //
  // This bit allows a component to raise an objection to the stopping of the
  // current phase. It affects only time consuming phases (such as the <run>
  // phase).
  //
  // When this bit is set, the <stop> task in the component is called as a result
  // of a call to <global_stop_request>. Components that are sensitive to an
  // immediate killing of its run-time processes should set this bit and
  // implement the stop task to prepare for shutdown.

  protected int enable_stop_interrupt = 0;


  // Function: resolve_bindings
  //
  // Processes all port, export, and imp connections. Checks whether each port's
  // min and max connection requirements are met.
  //
  // It is called just before the <end_of_elaboration> phase.
  //
  // Users should not call directly.

  extern virtual function void resolve_bindings ();



  //----------------------------------------------------------------------------
  // Group: Configuration Interface
  //----------------------------------------------------------------------------
  //
  // Components can be designed to be user-configurable in terms of its
  // topology (the type and number of children it has), mode of operation, and
  // run-time parameters (knobs). The configuration interface accommodates
  // this common need, allowing component composition and state to be modified
  // without having to derive new classes or new class hierarchies for
  // every configuration scenario. 
  //
  //----------------------------------------------------------------------------


  // Used for caching config settings
  static bit m_config_set = 1;

  // Function: set_config_int

  extern virtual function void set_config_int (string inst_name,  
                                               string field_name,
                                               ovm_bitstream_t value);

  // Function: set_config_string

  extern virtual function void set_config_string (string inst_name,  
                                                  string field_name,
                                                  string value);

  // Function: set_config_object
  //
  // Calling set_config_* causes configuration settings to be created and
  // placed in a table internal to this component. There are similar global
  // methods that store settings in a global table. Each setting stores the
  // supplied ~inst_name~, ~field_name~, and ~value~ for later use by descendent
  // components during their construction. (The global table applies to
  // all components and takes precedence over the component tables.)
  //
  // When a descendant component calls a get_config_* method, the ~inst_name~
  // and ~field_name~ provided in the get call are matched against all the
  // configuration settings stored in the global table and then in each
  // component in the parent hierarchy, top-down. Upon the first match, the
  // value stored in the configuration setting is returned. Thus, precedence is
  // global, following by the top-level component, and so on down to the
  // descendent component's parent.
  //
  // These methods work in conjunction with the get_config_* methods to
  // provide a configuration setting mechanism for integral, string, and
  // ovm_object-based types. Settings of other types, such as virtual interfaces
  // and arrays, can be indirectly supported by defining a class that contains
  // them.
  //
  // Both ~inst_name~ and ~field_name~ may contain wildcards.
  //
  // - For set_config_int, ~value~ is an integral value that can be anything
  //   from 1 bit to 4096 bits.
  //
  // - For set_config_string, ~value~ is a string.
  //
  // - For set_config_object, ~value~ must be an <ovm_object>-based object or
  //   null.  Its clone argument specifies whether the object should be cloned.
  //   If set, the object is cloned both going into the table (during the set)
  //   and coming out of the table (during the get), so that multiple components
  //   matched to the same setting (by way of wildcards) do not end up sharing
  //   the same object.
  //
  //   The following message tags are used for configuration setting. You can
  //   use the standard ovm report messaging interface to control these
  //   messages.
  //     CFGNTS    -- The configuration setting was not used by any component.
  //                  This is a warning.
  //     CFGOVR    -- The configuration setting was overridden by a setting above.
  //     CFGSET    -- The configuration setting was used at least once.
  //
  //
  // See <get_config_int>, <get_config_string>, and <get_config_object> for
  // information on getting the configurations set by these methods.


  extern virtual function void set_config_object (string inst_name,  
                                                  string field_name,
                                                  ovm_object value,  
                                                  bit clone=1);


  // Function: get_config_int

  extern virtual function bit get_config_int (string field_name,
                                              inout ovm_bitstream_t value);

  // Function: get_config_string

  extern virtual function bit get_config_string (string field_name,
                                                 inout string value);

  // Function: get_config_object
  //
  // These methods retrieve configuration settings made by previous calls to
  // their set_config_* counterparts. As the methods' names suggest, there is
  // direct support for integral types, strings, and objects.  Settings of other
  // types can be indirectly supported by defining an object to contain them.
  //
  // Configuration settings are stored in a global table and in each component
  // instance. With each call to a get_config_* method, a top-down search is
  // made for a setting that matches this component's full name and the given
  // ~field_name~. For example, say this component's full instance name is
  // top.u1.u2. First, the global configuration table is searched. If that
  // fails, then it searches the configuration table in component 'top',
  // followed by top.u1. 
  //
  // The first instance/field that matches causes ~value~ to be written with the
  // value of the configuration setting and 1 is returned. If no match
  // is found, then ~value~ is unchanged and the 0 returned.
  //
  // Calling the get_config_object method requires special handling. Because
  // ~value~ is an output of type <ovm_object>, you must provide an ovm_object
  // handle to assign to (_not_ a derived class handle). After the call, you can
  // then $cast to the actual type.
  //
  // For example, the following code illustrates how a component designer might
  // call upon the configuration mechanism to assign its ~data~ object property,
  // whose type myobj_t derives from ovm_object.
  //
  //|  class mycomponent extends ovm_component;
  //|
  //|    local myobj_t data;
  //|
  //|    function void build();
  //|      ovm_object tmp;
  //|      super.build();
  //|      if(get_config_object("data", tmp))
  //|        if (!$cast(data, tmp))
  //|          $display("error! config setting for 'data' not of type myobj_t");
  //|        endfunction
  //|      ...
  //
  // The above example overrides the <build> method. If you want to retain
  // any base functionality, you must call super.build().
  //
  // The ~clone~ bit clones the data inbound. The get_config_object method can
  // also clone the data outbound.
  //
  // See Members for information on setting the global configuration table.

  extern virtual function bit get_config_object (string field_name,
                                                 inout ovm_object value,  
                                                 input bit clone=1);


  // Function: check_config_usage
  //
  // Check all configuration settings in a components configuration table
  // to determine if the setting has been used, overridden or not used.
  // When ~recurse~ is 1 (default), configuration for this and all child
  // components are recursively checked. This function is automatically
  // called in the check phase, but can be manually called at any time.
  //
  // Additional detail is provided by the following message tags:
  // * CFGOVR -- lists all configuration settings that have been overridden
  // from above.  
  // * CFGSET -- lists all configuration settings that have been set.
  //
  // To get all configuration information prior to the run phase, do something 
  // like this in your top object:
  //|  function void start_of_simulation();
  //|    set_report_id_action_hier(CFGOVR, OVM_DISPLAY);
  //|    set_report_id_action_hier(CFGSET, OVM_DISPLAY);
  //|    check_config_usage();
  //|  endfunction

  extern function void check_config_usage (bit recurse=1);


  // Function: apply_config_settings
  //
  // Searches for all config settings matching this component's instance path.
  // For each match, the appropriate set_*_local method is called using the
  // matching config setting's field_name and value. Provided the set_*_local
  // method is implemented, the component property associated with the
  // field_name is assigned the given value. 
  //
  // This function is called by <ovm_component::build>.
  //
  // The apply_config_settings method determines all the configuration
  // settings targeting this component and calls the appropriate set_*_local
  // method to set each one. To work, you must override one or more set_*_local
  // methods to accommodate setting of your component's specific properties.
  // Any properties registered with the optional `ovm_*_field macros do not
  // require special handling by the set_*_local methods; the macros provide
  // the set_*_local functionality for you. 
  //
  // If you do not want apply_config_settings to be called for a component,
  // then the build() method should be overloaded and you should not call
  // super.build(). If this case, you must also set the m_build_done
  // bit. Likewise, apply_config_settings can be overloaded to customize
  // automated configuration.
  //
  // When the ~verbose~ bit is set, all overrides are printed as they are
  // applied. If the component's <print_config_matches> property is set, then
  // apply_config_settings is automatically called with ~verbose~ = 1.

  extern virtual function void apply_config_settings (bit verbose=0);


  // Function: print_config_settings
  //
  // Called without arguments, print_config_settings prints all configuration
  // information for this component, as set by previous calls to set_config_*.
  // The settings are printing in the order of their precedence.
  // 
  // If ~field~ is specified and non-empty, then only configuration settings
  // matching that field, if any, are printed. The field may not contain
  // wildcards. 
  //
  // If ~comp~ is specified and non-null, then the configuration for that
  // component is printed.
  //
  // If ~recurse~ is set, then configuration information for all ~comp~'s
  // children and below are printed as well.

  extern function void print_config_settings (string field="", 
                                              ovm_component comp=null, 
                                              bit recurse=0);


  // Variable: print_config_matches
  //
  // Setting this static variable causes get_config_* to print info about
  // matching configuration settings as they are being applied.

  static bit print_config_matches = 0; 


  //----------------------------------------------------------------------------
  // Group: Objection Interface
  //----------------------------------------------------------------------------
  //
  // These methods provide object level hooks into the <ovm_objection> 
  // mechanism.
  // 
  //----------------------------------------------------------------------------


  // Function: raised
  //
  // The raised callback is called when a decendant of the component instance
  // raises the specfied ~objection~. The ~source_obj~ is the object which
  // originally raised the object. ~count~ is an optional count that was used
  // to indicate a number of objections which were raised.

  virtual function void raised (ovm_objection objection, ovm_object source_obj, 
      int count);
  endfunction


  // Function: dropped
  //
  // The dropped callback is called when a decendant of the component instance
  // raises the specfied ~objection~. The ~source_obj~ is the object which
  // originally dropped the object. ~count~ is an optional count that was used
  // to indicate a number of objections which were dropped.

  virtual function void dropped (ovm_objection objection, ovm_object source_obj, 
      int count);
  endfunction


  // Task: all_dropped
  //
  // The all_dropped callback is called when a decendant of the component instance
  // raises the specfied ~objection~. The ~source_obj~ is the object which
  // originally all_dropped the object. ~count~ is an optional count that was used
  // to indicate a number of objections which were dropped. This callback is
  // time-consuming and the all_dropped conditional will not be propagated
  // up to the object's parent until the callback returns.

  virtual task all_dropped (ovm_objection objection, ovm_object source_obj, 
      int count);
  endtask


  //----------------------------------------------------------------------------
  // Group: Factory Interface
  //----------------------------------------------------------------------------
  //
  // The factory interface provides convenient access to a portion of OVM's
  // <ovm_factory> interface. For creating new objects and components, the
  // preferred method of accessing the factory is via the object or component
  // wrapper (see <ovm_component_registry #(T,Tname)> and
  // <ovm_object_registry #(T,Tname)>). The wrapper also provides functions
  // for setting type and instance overrides.
  //
  //----------------------------------------------------------------------------

  // Function: create_component
  //
  // A convenience function for <ovm_factory::create_component_by_name>,
  // this method calls upon the factory to create a new child component
  // whose type corresponds to the preregistered type name, ~requested_type_name~,
  // and instance name, ~name~. This method is equivalent to:
  //
  //|  factory.create_component_by_name(requested_type_name,
  //|                                   get_full_name(), name, this);
  //
  // If the factory determines that a type or instance override exists, the type
  // of the component created may be different than the requested type. See
  // <set_type_override> and <set_inst_override>. See also <ovm_factory> for
  // details on factory operation.

  extern function ovm_component create_component (string requested_type_name, 
                                                  string name);


  // Function: create_object
  //
  // A convenience function for <ovm_factory::create_object_by_name>,
  // this method calls upon the factory to create a new object
  // whose type corresponds to the preregistered type name,
  // ~requested_type_name~, and instance name, ~name~. This method is
  // equivalent to:
  //
  //|  factory.create_object_by_name(requested_type_name,
  //|                                get_full_name(), name);
  //
  // If the factory determines that a type or instance override exists, the
  // type of the object created may be different than the requested type.  See
  // <ovm_factory> for details on factory operation.

  extern function ovm_object create_object (string requested_type_name,
                                            string name="");


  // Function: set_type_override_by_type
  //
  // A convenience function for <ovm_factory::set_type_override_by_type>, this
  // method registers a factory override for components and objects created at
  // this level of hierarchy or below. This method is equivalent to:
  //
  //|  factory.set_type_override_by_type(original_type, override_type,replace);
  //
  // The ~relative_inst_path~ is relative to this component and may include
  // wildcards. The ~original_type~ represents the type that is being overridden.
  // In subsequent calls to <ovm_factory::create_object_by_type> or
  // <ovm_factory::create_component_by_type>, if the requested_type matches the
  // ~original_type~ and the instance paths match, the factory will produce
  // the ~override_type~. 
  //
  // The original and override type arguments are lightweight proxies to the
  // types they represent. See <set_inst_override_by_type> for information
  // on usage.

  extern static function void set_type_override_by_type
                                             (ovm_object_wrapper original_type, 
                                              ovm_object_wrapper override_type,
                                              bit replace=1);


  // Function: set_inst_override_by_type
  //
  // A convenience function for <ovm_factory::set_inst_override_by_type>, this
  // method registers a factory override for components and objects created at
  // this level of hierarchy or below. In typical usage, this method is
  // equivalent to:
  //
  //|  factory.set_inst_override_by_type({get_full_name(),".",
  //|                                     relative_inst_path},
  //|                                     original_type,
  //|                                     override_type);
  //
  // The ~relative_inst_path~ is relative to this component and may include
  // wildcards. The ~original_type~ represents the type that is being overridden.
  // In subsequent calls to <ovm_factory::create_object_by_type> or
  // <ovm_factory::create_component_by_type>, if the requested_type matches the
  // ~original_type~ and the instance paths match, the factory will produce the
  // ~override_type~. 
  //
  // The original and override types are lightweight proxies to the types they
  // represent. They can be obtained by calling type::get_type(), if
  // implemented, or by directly calling type::type_id::get(), where type is the
  // user type and type_id is the name of the typedef to
  // <ovm_object_registry #(T,Tname)> or <ovm_component_registry #(T,Tname)>.
  //
  // If you are employing the `ovm_*_utils macros, the typedef and the get_type
  // method will be implemented for you.
  //
  // The following example shows `ovm_*_utils usage:
  //
  //|  class comp extends ovm_component;
  //|    `ovm_component_utils(comp)
  //|    ...
  //|  endclass
  //|
  //|  class mycomp extends ovm_component;
  //|    `ovm_component_utils(mycomp)
  //|    ...
  //|  endclass
  //|
  //|  class block extends ovm_component;
  //|    `ovm_component_utils(block)
  //|    comp c_inst;
  //|    virtual function void build();
  //|      set_inst_override_by_type("c_inst",comp::get_type(),
  //|                                         mycomp::get_type());
  //|    endfunction
  //|    ...
  //|  endclass

  extern function void set_inst_override_by_type(string relative_inst_path,  
                                                 ovm_object_wrapper original_type,
                                                 ovm_object_wrapper override_type);


  // Function: set_type_override
  //
  // A convenience function for <ovm_factory::set_type_override_by_name>,
  // this method configures the factory to create an object of type
  // ~override_type_name~ whenever the factory is asked to produce a type
  // represented by ~original_type_name~.  This method is equivalent to:
  //
  //|  factory.set_type_override_by_name(original_type_name,
  //|                                    override_type_name, replace);
  //
  // The ~original_type_name~ typically refers to a preregistered type in the
  // factory. It may, however, be any arbitrary string. Subsequent calls to
  // create_component or create_object with the same string and matching
  // instance path will produce the type represented by override_type_name.
  // The ~override_type_name~ must refer to a preregistered type in the factory. 

  extern static function void set_type_override(string original_type_name, 
                                                string override_type_name,
                                                bit    replace=1);


  // Function: set_inst_override
  //
  // A convenience function for <ovm_factory::set_inst_override_by_type>, this
  // method registers a factory override for components created at this level
  // of hierarchy or below. In typical usage, this method is equivalent to:
  //
  //|  factory.set_inst_override_by_name({get_full_name(),".",
  //|                                     relative_inst_path},
  //|                                      original_type_name,
  //|                                     override_type_name);
  //
  // The ~relative_inst_path~ is relative to this component and may include
  // wildcards. The ~original_type_name~ typically refers to a preregistered type
  // in the factory. It may, however, be any arbitrary string. Subsequent calls
  // to create_component or create_object with the same string and matching
  // instance path will produce the type represented by ~override_type_name~.
  // The ~override_type_name~ must refer to a preregistered type in the factory. 

  extern function void set_inst_override(string relative_inst_path,  
                                         string original_type_name,
                                         string override_type_name);


  // Function: print_override_info
  //
  // This factory debug method performs the same lookup process as create_object
  // and create_component, but instead of creating an object, it prints
  // information about what type of object would be created given the
  // provided arguments.

  extern function void print_override_info(string requested_type_name,
                                           string name="");


  //----------------------------------------------------------------------------
  // Group: Hierarchical Reporting Interface
  //----------------------------------------------------------------------------
  //
  // This interface provides versions of the set_report_* methods in the
  // <ovm_report_object> base class that are applied recursively to this
  // component and all its children.
  //
  // When a report is issued and its associated action has the LOG bit set, the
  // report will be sent to its associated FILE descriptor.
  //----------------------------------------------------------------------------

  // Function: set_report_severity_action_hier

  extern function void set_report_severity_action_hier (ovm_severity severity,
                                                        ovm_action action);

  // Function: set_report_id_action_hier

  extern function void set_report_id_action_hier (string id,
                                                  ovm_action action);

  // Function: set_report_severity_id_action_hier
  //
  // These methods recursively associate the specified action with reports of
  // the given ~severity~, ~id~, or ~severity-id~ pair. An action associated
  // with a particular severity-id pair takes precedence over an action
  // associated with id, which takes precedence over an an action associated
  // with a severity.
  //
  // For a list of severities and their default actions, refer to
  // <ovm_report_handler>.

  extern function void set_report_severity_id_action_hier(ovm_severity severity,
                                                          string id,
                                                          ovm_action action);



  // Function: set_report_default_file_hier

  extern function void set_report_default_file_hier (OVM_FILE file);

  // Function: set_report_severity_file_hier

  extern function void set_report_severity_file_hier (ovm_severity severity,
                                                      OVM_FILE file);

  // Function: set_report_id_file_hier

  extern function void set_report_id_file_hier (string id,
                                                OVM_FILE file);

  // Function: set_report_severity_id_file_hier
  //
  // These methods recursively associate the specified FILE descriptor with
  // reports of the given ~severity~, ~id~, or ~severity-id~ pair. A FILE
  // associated with a particular severity-id pair takes precedence over a FILE
  // associated with id, which take precedence over an a FILE associated with a
  // severity, which takes precedence over the default FILE descriptor.
  //
  // For a list of severities and other information related to the report
  // mechanism, refer to <ovm_report_handler>.

  extern function void set_report_severity_id_file_hier(ovm_severity severity,
                                                        string id,
                                                        OVM_FILE file);


  // Function: set_report_verbosity_level_hier
  //
  // This method recursively sets the maximum verbosity level for reports for
  // this component and all those below it. Any report from this component
  // subtree whose verbosity exceeds this maximum will be ignored.
  // 
  // See <ovm_report_handler> for a list of predefined message verbosity levels
  // and their meaning.

    extern function void set_report_verbosity_level_hier (int verbosity);
  

  //----------------------------------------------------------------------------
  // Group: Recording Interface
  //----------------------------------------------------------------------------
  // These methods comprise the component-based transaction recording
  // interface. The methods can be used to record the transactions that
  // this component "sees", i.e. produces or consumes.
  //
  // The API and implementation are subject to change once a vendor-independent
  // use-model is determined.
  //----------------------------------------------------------------------------

  // Function: accept_tr
  //
  // This function marks the acceptance of a transaction, ~tr~, by this
  // component. Specifically, it performs the following actions:
  //
  // - Calls the ~tr~'s <ovm_transaction::accept_tr> method, passing to it the
  //   ~accept_time~ argument.
  //
  // - Calls this component's <do_accept_tr> method to allow for any post-begin
  //   action in derived classes.
  //
  // - Triggers the component's internal accept_tr event. Any processes waiting
  //   on this event will resume in the next delta cycle. 

  extern function void accept_tr (ovm_transaction tr, time accept_time=0);


  // Function: do_accept_tr
  //
  // The <accept_tr> method calls this function to accommodate any user-defined
  // post-accept action. Implementations should call super.do_accept_tr to
  // ensure correct operation.
    
  extern virtual protected function void do_accept_tr (ovm_transaction tr);


  // Function: begin_tr
  //
  // This function marks the start of a transaction, ~tr~, by this component.
  // Specifically, it performs the following actions:
  //
  // - Calls ~tr~'s <ovm_transaction::begin_tr> method, passing to it the
  //   ~begin_time~ argument. The ~begin_time~ should be greater than or equal
  //   to the accept time. By default, when ~begin_time~ = 0, the current
  //   simulation time is used.
  //
  //   If recording is enabled (recording_detail != OVM_OFF), then a new
  //   database-transaction is started on the component's transaction stream
  //   given by the stream argument. No transaction properties are recorded at
  //   this time.
  //
  // - Calls the component's <do_begin_tr> method to allow for any post-begin
  //   action in derived classes.
  //
  // - Triggers the component's internal begin_tr event. Any processes waiting
  //   on this event will resume in the next delta cycle. 
  //
  // A handle to the transaction is returned. The meaning of this handle, as
  // well as the interpretation of the arguments ~stream_name~, ~label~, and
  // ~desc~ are vendor specific.

  extern function integer begin_tr (ovm_transaction tr,
                                    string stream_name="main",
                                    string label="",
                                    string desc="",
                                    time begin_time=0);


  // Function: begin_child_tr
  //
  // This function marks the start of a child transaction, ~tr~, by this
  // component. Its operation is identical to that of <begin_tr>, except that
  // an association is made between this transaction and the provided parent
  // transaction. This association is vendor-specific.

  extern function integer begin_child_tr (ovm_transaction tr,
                                          integer parent_handle=0,
                                          string stream_name="main",
                                          string label="",
                                          string desc="",
                                          time begin_time=0);


  // Function: do_begin_tr
  //
  // The <begin_tr> and <begin_child_tr> methods call this function to
  // accommodate any user-defined post-begin action. Implementations should call
  // super.do_begin_tr to ensure correct operation.

  extern virtual protected 
                 function void do_begin_tr (ovm_transaction tr,
                                            string stream_name,
                                            integer tr_handle);


  // Function: end_tr
  //
  // This function marks the end of a transaction, ~tr~, by this component.
  // Specifically, it performs the following actions:
  //
  // - Calls ~tr~'s <ovm_transaction::end_tr> method, passing to it the
  //   ~end_time~ argument. The ~end_time~ must at least be greater than the
  //   begin time. By default, when ~end_time~ = 0, the current simulation time
  //   is used.
  //
  //   The transaction's properties are recorded to the database-transaction on
  //   which it was started, and then the transaction is ended. Only those
  //   properties handled by the transaction's do_record method (and optional
  //   `ovm_*_field macros) are recorded.
  //
  // - Calls the component's <do_end_tr> method to accommodate any post-end
  //   action in derived classes.
  //
  // - Triggers the component's internal end_tr event. Any processes waiting on
  //   this event will resume in the next delta cycle. 
  //
  // The ~free_handle~ bit indicates that this transaction is no longer needed.
  // The implementation of free_handle is vendor-specific.

  extern function void end_tr (ovm_transaction tr,
                               time end_time=0,
                               bit free_handle=1);


  // Function: do_end_tr
  //
  // The <end_tr> method calls this function to accommodate any user-defined
  // post-end action. Implementations should call super.do_end_tr to ensure
  // correct operation.

  extern virtual protected function void do_end_tr (ovm_transaction tr,
                                                    integer tr_handle);


  // Function: record_error_tr
  //
  // This function marks an error transaction by a component. Properties of the
  // given ovm_object, ~info~, as implemented in its <do_record> method, are
  // recorded to the transaction database.
  //
  // An ~error_time~ of 0 indicates to use the current simulation time. The
  // ~keep_active~ bit determines if the handle should remain active. If 0,
  // then a zero-length error transaction is recorded. A handle to the
  // database-transaction is returned. 
  //
  // Interpretation of this handle, as well as the strings ~stream_name~,
  // ~label~, and ~desc~, are vendor-specific.

  extern function integer record_error_tr (string stream_name="main",
                                           ovm_object info=null,
                                           string label="error_tr",
                                           string desc="",
                                           time   error_time=0,
                                           bit    keep_active=0);


  // Function: record_event_tr
  //
  // This function marks an event transaction by a component. 
  //
  // An ~event_time~ of 0 indicates to use the current simulation time. 
  //
  // A handle to the transaction is returned. The ~keep_active~ bit determines
  // if the handle may be used for other vendor-specific purposes. 
  //
  // The strings for ~stream_name~, ~label~, and ~desc~ are vendor-specific
  // identifiers for the transaction.

  extern function integer record_event_tr (string stream_name="main",
                                           ovm_object info=null,
                                           string label="event_tr",
                                           string desc="",
                                           time   event_time=0,
                                           bit    keep_active=0);


  // Variable: print_enabled
  //
  // This bit determines if this component should automatically be printed as a
  // child of its parent object. 
  // 
  // By default, all children are printed. However, this bit allows a parent
  // component to disable the printing of specific children.

  bit print_enabled = 1;


  //----------------------------------------------------------------------------
  //                     PRIVATE or PSUEDO-PRIVATE members
  //                      *** Do not call directly ***
  //         Implementation and even existence are subject to change. 
  //----------------------------------------------------------------------------
  // Most local methods are prefixed with m_, indicating they are not
  // user-level methods. SystemVerilog does not support friend classes,
  // which forces some otherwise internal methods to be exposed (i.e. not
  // be protected via 'local' keyword). These methods are also prefixed
  // with m_ to indicate they are not intended for public use.
  //
  // Internal methods will not be documented, although their implementa-
  // tions are freely available via the open-source license.
  //----------------------------------------------------------------------------

  extern local function void m_component_path (ref ovm_component path[$]);
  extern local function void m_get_config_matches
                             (ref ovm_config_setting cfg_matches[$], 
                              input ovm_config_setting::ovm_config_type cfgtype, 
                              string field_name);

  /*protected*/ ovm_component m_parent;
  protected ovm_component m_children[string];
  protected ovm_component m_children_by_handle[ovm_component];
  extern local function bit m_add_child (ovm_component child);
  extern virtual local function void m_set_full_name ();

  extern virtual function void  do_func_phase (ovm_phase phase);
  extern virtual task do_task_phase (ovm_phase phase);

  extern          function void  do_resolve_bindings ();
  extern          function void  do_flush();

  extern virtual function void flush ();

  ovm_phase m_curr_phase=null;

  protected ovm_config_setting m_configuration_table[$];

  protected bit m_build_done=0;

  extern local function void m_extract_name(string name ,
                                            output string leaf ,
                                            output string remainder );
  local static bit m_phases_loaded = 0;

  // overridden to disable
  extern virtual function ovm_object create (string name=""); 
  extern virtual function ovm_object clone  ();

  local integer m_stream_handle[string];
  local integer m_tr_h[ovm_transaction];
  extern protected function integer m_begin_tr (ovm_transaction tr,
              integer parent_handle=0, bit has_parent=0,
              string stream_name="main", string label="",
              string desc="", time begin_time=0);

  `ifndef INCA
  protected process m_phase_process;
  `endif
  protected event m_kill_request;

  string m_name;

  protected ovm_event_pool event_pool;


  extern virtual task restart ();

  //----------------------------------------------------------------------------
  //                          DEPRECATED MEMBERS
  //                      *** Do not use in new code ***
  //                  Convert existing code when appropriate.
  //----------------------------------------------------------------------------
  // Deprecated static methods:
  // 
  // global_stop_request
  //   replaced by ovm_top.stop_request
  //
  // Deprecated phases:
  //
  // post_new
  //   replaced by build (top-down)
  //
  // import/export_connections
  //   Consolidated into the connect phase; deferred binding enforcement
  //   via resolve_bindings allows connections to be order-independent
  //
  // pre_run
  //   replaced by start_of_simulation
  //----------------------------------------------------------------------------

  extern static  function  void  global_stop_request();

  extern virtual function  void  post_new ();
  extern virtual function  void  import_connections ();
  extern virtual function  void  configure ();
  extern virtual function  void  export_connections ();
  extern virtual function  void  pre_run (); 

  extern static  function ovm_component find_component   (string comp_match);
  extern static  function void          find_components  (string comp_match, 
                                                    ref ovm_component comps[$]);
  extern static  function ovm_component get_component    (int ele);
  extern static  function int           get_num_components ();

  `include "compatibility/urm_message_compatibility.svh"

endclass : ovm_component

// for backward compatibility
typedef ovm_component ovm_threaded_component;
            
`endif // OVM_COMPONENT_SVH

