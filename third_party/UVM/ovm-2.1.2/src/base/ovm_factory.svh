// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_factory.svh#21 $
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

`ifndef OVM_FACTORY_SVH
`define OVM_FACTORY_SVH

typedef class ovm_object;
typedef class ovm_component;
typedef class ovm_object_wrapper;
typedef class ovm_factory_override;

//Instance overrides by requested type lookup
class ovm_factory_queue_class;
  ovm_factory_override queue[$];
endclass

// Title: OVM Factory
//
// This page covers the following classes.
//
// - <ovm_factory> - creates objects and components according to user-defined
// type and instance-based overrides.
//
// - <ovm_object_wrapper> - a lightweight substitute (proxy) representing a
// user-defined object or component.



//------------------------------------------------------------------------------
//
// CLASS: ovm_factory
//
//------------------------------------------------------------------------------
//
// As the name implies, ovm_factory is used to manufacture (create) OVM objects
// and components. Only one instance of the factory is present in a given
// simulation (termed a singleton). Object and component types are registered
// with the factory using lightweight proxies to the actual objects and
// components being created. The <ovm_object_registry #(T,Tname)> and
// <ovm_component_registry #(T,Tname)> class are used to proxy <ovm_objects>
// and <ovm_components>.
//
// The factory provides both name-based and type-based interfaces.
//
// type-based - The type-based interface is far less prone to errors in usage.
//   When errors do occur, they are caught at compile-time.
//
// name-based - The name-based interface is dominated 
//   by string arguments that can be misspelled and provided in the wrong order.
//   Errors in name-based requests might only be caught at the time of the call,
//   if at all. Further, the name-based interface is not portable across
//   simulators when used with parameterized classes.
//
// See <Usage> section for details on configuring and using the factory.
//

class ovm_factory;

  extern `_protected function new ();

  extern static function ovm_factory get();

  // Group: Registering Types

  // Function: register
  //
  // Registers the given proxy object, ~obj~, with the factory. The proxy object
  // is a lightweight substitute for the component or object it represents. When
  // the factory needs to create an object of a given type, it calls the proxy's
  // create_object or create_component method to do so.
  //
  // When doing name-based operations, the factory calls the proxy's
  // get_type_name method to match against the ~requested_type_name~ argument in
  // subsequent calls to <create_component_by_name> and <create_object_by_name>.
  // If the proxy object's get_type_name method returns the empty string,
  // name-based lookup is effectively disabled.

  extern function void register (ovm_object_wrapper obj);


  // Group: Type & Instance Overrides

  // Function: set_inst_override_by_type

  extern function
      void set_inst_override_by_type (ovm_object_wrapper original_type,
                                      ovm_object_wrapper override_type,
                                      string full_inst_path);

  // Function: set_inst_override_by_name
  //
  // Configures the factory to create an object of the override's type whenever
  // a request is made to create an object of the original type using a context
  // that matches ~full_inst_path~. The original type is typically a super class
  // of the override type.
  //
  // When overriding by type, the ~original_type~ and ~override_type~ are
  // handles to the types' proxy objects. Preregistration is not required.
  //
  // When overriding by name, the ~original_type_name~ typically refers to a
  // preregistered type in the factory. It may, however, be any arbitrary
  // string. Future calls to any of the create_* methods with the same string
  // and matching instance path will produce the type represented by
  // ~override_type_name~, which must be preregistered with the factory.
  //
  // The ~full_inst_path~ is matched against the contentation of
  // {~parent_inst_path~, ".", ~name~} provided in future create requests. The
  // ~full_inst_path~ may include wildcards (* and ?) such that a single
  // instance override can be applied in multiple contexts. A ~full_inst_path~
  // of "*" is effectively a type override, as it will match all contexts.
  //
  // When the factory processes instance overrides, the instance queue is
  // processed in order of override registrations, and the first override
  // match prevails. Thus, more specific overrides should be registered
  // first, followed by more general overrides.

  extern function
      void set_inst_override_by_name (string original_type_name,
                                      string override_type_name,
                                      string full_inst_path);


  // Function: set_type_override_by_type

  extern function
      void set_type_override_by_type (ovm_object_wrapper original_type,
                                      ovm_object_wrapper override_type,
                                      bit replace=1);

  // Function: set_type_override_by_name
  //
  // Configures the factory to create an object of the override's type whenever
  // a request is made to create an object of the original type, provided no
  // instance override applies. The original type is typically a super class of
  // the override type.
  //
  // When overriding by type, the ~original_type~ and ~override_type~ are
  // handles to the types' proxy objects. Preregistration is not required.
  //
  // When overriding by name, the ~original_type_name~ typically refers to a
  // preregistered type in the factory. It may, however, be any arbitrary
  // string. Future calls to any of the create_* methods with the same string
  // and matching instance path will produce the type represented by
  // ~override_type_name~, which must be preregistered with the factory.
  //
  // When ~replace~ is 1, a previous override on ~original_type_name~ is
  // replaced, otherwise a previous override, if any, remains intact.

  extern function
      void set_type_override_by_name (string original_type_name,
                                      string override_type_name,
                                      bit replace=1);


  // Group: Creation

  // Function: create_object_by_type

  extern function
      ovm_object    create_object_by_type    (ovm_object_wrapper requested_type,  
                                              string parent_inst_path="",
                                              string name=""); 

  // Function: create_component_by_type

  extern function
      ovm_component create_component_by_type (ovm_object_wrapper requested_type,  
                                              string parent_inst_path="",
                                              string name, 
                                              ovm_component parent);

  // Function: create_object_by_name

  extern function
      ovm_object    create_object_by_name    (string requested_type_name,  
                                              string parent_inst_path="",
                                              string name=""); 

  // Function: create_component_by_name
  //
  // Creates and returns a component or object of the requested type, which may
  // be specified by type or by name. A requested component must be derived
  // from the <ovm_component> base class, and a requested object must be derived
  // from the <ovm_object> base class.
  //
  // When requesting by type, the ~requested_type~ is a handle to the type's
  // proxy object. Preregistration is not required.
  //
  // When requesting by name, the ~request_type_name~ is a string representing
  // the requested type, which must have been registered with the factory with
  // that name prior to the request. If the factory does not recognize the
  // ~requested_type_name~, an error is produced and a null handle returned.
  //
  // If the optional ~parent_inst_path~ is provided, then the concatenation,
  // {~parent_inst_path~, ".",~name~}, forms an instance path (context) that
  // is used to search for an instance override. The ~parent_inst_path~ is
  // typically obtained by calling the <ovm_component::get_full_name> on the
  // parent.
  //
  // If no instance override is found, the factory then searches for a type
  // override.
  //
  // Once the final override is found, an instance of that component or object
  // is returned in place of the requested type. New components will have the
  // given ~name~ and ~parent~. New objects will have the given ~name~, if
  // provided.
  //
  // Override searches are recursively applied, with instance overrides taking
  // precedence over type overrides. If ~foo~ overrides ~bar~, and ~xyz~
  // overrides ~foo~, then a request for ~bar~ will produce ~xyz~. Recursive
  // loops will result in an error, in which case the type returned will be
  // that which formed the loop. Using the previous example, if ~bar~
  // overrides ~xyz~, then ~bar~ is returned after the error is issued.

  extern function
      ovm_component create_component_by_name (string requested_type_name,  
                                              string parent_inst_path="",
                                              string name, 
                                              ovm_component parent);

  // Group: Debug

  // Function: debug_create_by_type

  extern function
      void debug_create_by_type (ovm_object_wrapper requested_type,
                                 string parent_inst_path="",
                                 string name="");

  // Function: debug_create_by_name
  //
  // These methods perform the same search algorithm as the create_* methods,
  // but they do not create new objects. Instead, they provide detailed
  // information about what type of object it would return, listing each
  // override that was applied to arrive at the result. Interpretation of the
  // arguments are exactly as with the create_* methods.

  extern function
      void debug_create_by_name (string requested_type_name,
                                 string parent_inst_path="",
                                 string name="");

                   
  // Function: find_override_by_type

  extern function
      ovm_object_wrapper find_override_by_type (ovm_object_wrapper requested_type,
                                                string full_inst_path);

  // Function: find_override_by_name
  //
  // These methods return the proxy to the object that would be created given
  // the arguments. The ~full_inst_path~ is typically derived from the parent's
  // instance path and the leaf name of the object to be created, i.e.
  // { parent.get_full_name(), ".", name }.

  extern function
      ovm_object_wrapper find_override_by_name (string requested_type_name,
                                                string full_inst_path);

  extern
    function ovm_object_wrapper find_by_name            (string type_name);

  // Function: print
  //
  // Prints the state of the ovm_factory, including registered types, instance
  // overrides, and type overrides.
  //
  // When ~all_types~ is 0, only type and instance overrides are displayed. When
  // ~all_types~ is 1 (default), all registered user-defined types are printed as
  // well, provided they have names associated with them. When ~all_types~ is 2,
  // the OVM types (prefixed with ovm_) are included in the list of registered
  // types.

  extern function void print (int all_types=1);


  //-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_

  // name-based static methods - deprecated

  extern static
      function void         set_type_override (string original_type_name,
                                               string override_type_name,
                                               bit    replace=1);

  extern static
      function void         set_inst_override (string full_inst_path,
                                               string original_type_name,
                                               string override_type_name);

  extern static
      function ovm_object    create_object    (string requested_type_name,  
                                               string parent_inst_path="",
                                               string name="");

  extern static
      function ovm_component create_component (string requested_type_name,
                                               string parent_inst_path="",
                                               string name, 
                                               ovm_component parent);


  extern static
      function void       print_override_info (string requested_type_name,
                                               string parent_inst_path="",
                                               string name="");

  extern static function void  print_all_overrides(int all_types=0);

  extern static function void  auto_register (ovm_object_wrapper obj);


  //----------------------------------------------------------------------------
  // PRIVATE MEMBERS
  
  extern protected
      function void  m_debug_create (string requested_type_name,
                                     ovm_object_wrapper requested_type,
                                     string parent_inst_path,
                                     string name);
  
  extern protected
      function void  m_debug_display(string requested_type_name,
                                     ovm_object_wrapper result,
                                     string full_inst_path);
  static local ovm_factory m_inst;

  protected bit                  m_types[ovm_object_wrapper];
  protected bit                  m_lookup_strs[string];
  protected ovm_object_wrapper   m_type_names[string];

  protected ovm_factory_override m_type_overrides[$];

  protected ovm_factory_queue_class m_inst_override_queues[ovm_object_wrapper];
  protected ovm_factory_queue_class m_inst_override_name_queues[string];
  protected ovm_factory_override    m_wildcard_inst_overrides[$];

  local ovm_factory_override     m_override_info[$];
  local static bit m_debug_pass;

  extern function bit m_has_wildcard(string nm);

  extern function bit check_inst_override_exists
                                      (ovm_object_wrapper original_type,
                                       ovm_object_wrapper override_type,
                                       string full_inst_path);

endclass


//------------------------------------------------------------------------------
//
// Group: Usage
//
// Using the factory involves three basic operations
//
// 1 - Registering objects and components types with the factory
// 2 - Designing components to use the factory to create objects or components
// 3 - Configuring the factory with type and instance overrides, both within and
//     outside components
//
// We'll briefly cover each of these steps here. More reference information can
// be found at <Utility Macros>, <ovm_component_registry #(T,Tname)>,
// <ovm_object_registry #(T,Tname)>, <ovm_component>.
//
// 1 -- Registering objects and component types with the factory:
//
// When defining <ovm_object> and <ovm_component>-based classes, simply invoke
// the appropriate macro. Use of macros are required to ensure portability
// across different vendors' simulators.
//
// Objects that are not parameterized are declared as
//
//|  class packet extends ovm_object;
//|    `ovm_object_utils(packet)
//|  endclass
//|
//|  class packetD extends packet;
//|    `ovm_object_utils(packetD)
//|  endclass
//
// Objects that are parameterized are declared as
//
//|  class packet #(type T=int, int WIDTH=32) extends ovm_object;
//|    `ovm_object_param_utils(packet #(T,WIDTH))
//|   endclass
//
// Components that are not parameterized are declared as
//
//|  class comp extends ovm_component;
//|    `ovm_component_utils(comp)
//|  endclass
//
// Components that are parameterized are declared as
//
//|  class comp #(type T=int, int WIDTH=32) extends ovm_component;
//|    `ovm_component_param_utils(comp #(T,WIDTH))
//|  endclass
//
// The `ovm_*_utils macros for simple, non-parameterized classes will register
// the type with the factory and define the get_type, get_type_name, and create
// virtual methods inherited from <ovm_object>. It will also define a static
// type_name variable in the class, which will allow you to determine the type
// without having to allocate an instance. 
//
// The `ovm_*_param_utils macros for parameterized classes differ from
// `ovm_*_utils classes in the following ways:
//
// - The get_type_name method and static type_name variable are not defined. You
//   will need to implement these manually.
//
// - A type name is not associated with the type when registeriing with the
//   factory, so the factory's *_by_name operations will not work with
//   parameterized classes.
//
// - The factory's <print>, <debug_create_by_type>, and <debug_create_by_name>
//   methods, which depend on type names to convey information, will list
//   parameterized types as <unknown>.
//
// It is worth noting that environments that exclusively use the type-based
// factory methods (*_by_type) do not require type registration. The factory's
// type-based methods will register the types involved "on the fly," when first
// used. However, registering with the `ovm_*_utils macros enables name-based
// factory usage and implements some useful utility functions.
//
//
// 2 -- Designing components that defer creation to the factory:
//
// Having registered your objects and components with the factory, you can now
// make requests for new objects and components via the factory. Using the factory
// instead of allocating them directly (via new) allows different objects to be
// substituted for the original without modifying the requesting class. The
// following code defines a driver class that is parameterized.
//
//|  class driverB #(type T=ovm_object) extends ovm_driver;
//|
//|    // parameterized classes must use the _param_utils version
//|    `ovm_component_param_utils(driverB #(T))
//|
//|    // our packet type; this can be overridden via the factory
//|    T pkt;
//|
//|    // standard component constructor
//|    function new(string name, ovm_component parent=null);
//|      super.new(name,parent);
//|    endfunction
//|
//|    // get_type_name not implemented by macro for parameterized classes
//|    const static string type_name = {"driverB #(",T::type_name,")"};
//|    virtual function string get_type_name();
//|      return type_name;
//|    endfunction
//|
//|    // using the factory allows pkt overrides from outside the class
//|    virtual function void build();
//|      pkt = packet::type_id::create("pkt",this);
//|    endfunction
//|
//|    // print the packet so we can confirm its type when printing
//|    virtual function void do_print(ovm_printer printer);
//|      printer.print_object("pkt",pkt);
//|    endfunction
//|
//|  endclass
//
// For purposes of illustrating type and instance overrides, we define two
// subtypes of the ~driverB~ class. The subtypes are also parameterized, so
// we must again provide an implementation for <ovm_object::get_type_name>,
// which we recommend writing in terms of a static string constant.
//
//|  class driverD1 #(type T=ovm_object) extends driverB #(T);
//|
//|    `ovm_component_param_utils(driverD1 #(T))
//|
//|    function new(string name, ovm_component parent=null);
//|      super.new(name,parent);
//|    endfunction
//|
//|    const static string type_name = {"driverD1 #(",T::type_name,")"};
//|    virtual function string get_type_name();
//|      ...return type_name;
//|    endfunction
//|
//|  endclass
//|
//|  class driverD2 #(type T=ovm_object) extends driverB #(T);
//|
//|    `ovm_component_param_utils(driverD2 #(T))
//|
//|    function new(string name, ovm_component parent=null);
//|      super.new(name,parent);
//|    endfunction
//|
//|    const static string type_name = {"driverD2 #(",T::type_name,")"};
//|    virtual function string get_type_name();
//|      return type_name;
//|    endfunction
//|
//|  endclass
//|
//|  // typedef some specializations for convenience
//|  typedef driverB  #(packet) B_driver;   // the base driver
//|  typedef driverD1 #(packet) D1_driver;  // a derived driver
//|  typedef driverD2 #(packet) D2_driver;  // another derived driver
//
// Next, we'll define a agent component, which requires a utils macro for
// non-parameterized types. Before creating the drivers using the factory, we
// override ~driver0~'s packet type to be ~packetD~.
//
//|  class agent extends ovm_agent;
//|
//|    `ovm_component_utils(agent)
//|    ...
//|    B_driver driver0;
//|    B_driver driver1;
//|
//|    function new(string name, ovm_component parent=null);
//|      super.new(name,parent);
//|    endfunction
//|
//|    virtual function void build();
//|
//|      // override the packet type for driver0 and below
//|      packet::type_id::set_inst_override(packetD::get_type(),"driver0.*");
//|
//|      // create using the factory; actual driver types may be different
//|      driver0 = B_driver::type_id::create("driver0",this);
//|      driver1 = B_driver::type_id::create("driver1",this);
//|
//|    endfunction
//|
//|  endclass
//
// Finally we define an environment class, also not parameterized. Its build
// method shows three methods for setting an instance override on a grandchild
// component with relative path name, ~agent1.driver1~, all equivalent.
//
//|  class env extends ovm_env;
//|
//|    `ovm_component_utils(env)
//|
//|    agent agent0;
//|    agent agent1;
//|
//|    function new(string name, ovm_component parent=null);
//|      super.new(name,parent);
//|    endfunction
//|
//|    virtual function void build();
//|
//|      // three methods to set an instance override for agent1.driver1
//|      // - via component convenience method...
//|      set_inst_override_by_type("agent1.driver1",
//|                                B_driver::get_type(),
//|                                D2_driver::get_type());
//|
//|      // - via the component's proxy (same approach as create)...
//|      B_driver::type_id::set_inst_override(D2_driver::get_type(),
//|                                           "agent1.driver1",this);
//|
//|      // - via a direct call to a factory method...
//|      factory.set_inst_override_by_type(B_driver::get_type(),
//|                                        D2_driver::get_type(),
//|                                        {get_full_name(),".agent1.driver1"});
//|
//|      // create agents using the factory; actual agent types may be different
//|      agent0 = agent::type_id::create("agent0",this);
//|      agent1 = agent::type_id::create("agent1",this);
//|
//|    endfunction
//|
//|    // at end_of_elaboration, print topology and factory state to verify
//|    virtual function void end_of_elaboration();
//|      ovm_top.print_topology();
//|    endfunction
//|
//|    virtual task run();
//|      #100 global_stop_request();
//|    endfunction
//|
//|  endclass
//   
//
// 3 -- Configuring the factory with type and instance overrides:
//
// In the previous step, we demonstrated setting instance overrides and creating
// components using the factory within component classes. Here, we will
// demonstrate setting overrides from outside components, as when initializing
// the environment prior to running the test.
//
//|  module top;
//|
//|    env env0;
//|
//|    initial begin
//|
//|      // Being registered first, the following overrides take precedence
//|      // over any overrides made within env0's construction & build.
//|
//|      // Replace all base drivers with derived drivers...
//|      B_driver::type_id::set_type_override(D_driver::get_type());
//|
//|      // ...except for agent0.driver0, whose type remains a base driver.
//|      //     (Both methods below have the equivalent result.)
//|
//|      // - via the component's proxy (preferred)
//|      B_driver::type_id::set_inst_override(B_driver::get_type(),
//|                                           "env0.agent0.driver0");
//|
//|      // - via a direct call to a factory method
//|      factory.set_inst_override_by_type(B_driver::get_type(),
//|                                        B_driver::get_type(),
//|                                    {get_full_name(),"env0.agent0.driver0"});
//|
//|      // now, create the environment; our factory configuration will
//|      // govern what topology gets created
//|      env0 = new("env0");
//|
//|      // run the test (will execute build phase)
//|      run_test();
//|
//|    end
//|
//|  endmodule
//
// When the above example is run, the resulting topology (displayed via a call to
// <ovm_top.print_topology> in env's <ovm_component::end_of_elaboration> method)
// is similar to the following:
//
//| # OVM_INFO @ 0 [RNTST] Running test ...
//| # OVM_INFO @ 0 [OVMTOP] OVM testbench topology:
//| # ----------------------------------------------------------------------
//| # Name                     Type                Size                Value
//| # ----------------------------------------------------------------------
//| # env0                     env                 -                  env0@2
//| #   agent0                 agent               -                agent0@4
//| #     driver0              driverB #(packet)   -               driver0@8
//| #       pkt                packet              -                  pkt@21
//| #     driver1              driverD #(packet)   -              driver1@14
//| #       pkt                packet              -                  pkt@23
//| #   agent1                 agent               -                agent1@6
//| #     driver0              driverD #(packet)   -              driver0@24
//| #       pkt                packet              -                  pkt@37
//| #     driver1              driverD2 #(packet)  -              driver1@30
//| #       pkt                packet              -                  pkt@39
//| # ----------------------------------------------------------------------
// 
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------
//
// CLASS: ovm_object_wrapper
//
// The ovm_object_wrapper provides an abstract interface for creating object and
// component proxies. Instances of these lightweight proxies, representing every
// <ovm_object>-based and <ovm_component>-based object available in the test
// environment, are registered with the <ovm_factory>. When the factory is
// called upon to create an object or component, it finds and delegates the
// request to the appropriate proxy.
//
//------------------------------------------------------------------------------

virtual class ovm_object_wrapper;

  // Function: create_object
  //
  // Creates a new object with the optional ~name~.
  // An object proxy (e.g., <ovm_object_registry #(T,Tname)>) implements this
  // method to create an object of a specific type, T.

  virtual function ovm_object create_object (string name="");
    return null;
  endfunction


  // Function: create_component
  //
  // Creates a new component, passing to its constructor the given ~name~ and
  // ~parent~. A component proxy (e.g. <ovm_component_registry #(T,Tname)>)
  // implements this method to create a component of a specific type, T.

  virtual function ovm_component create_component (string name, 
                                                   ovm_component parent); 
    return null;
  endfunction


  // Function: get_type_name
  // 
  // Derived classes implement this method to return the type name of the object
  // created by <create_component> or <create_object>. The factory uses this
  // name when matching against the requested type in name-based lookups.

  pure virtual function string get_type_name();

endclass


//------------------------------------------------------------------------------
//
// CLASS- ovm_factory_override
//
// Internal class.
//------------------------------------------------------------------------------

class ovm_factory_override;
  string full_inst_path;
  string orig_type_name;
  string ovrd_type_name;
  bit selected;
  ovm_object_wrapper orig_type;
  ovm_object_wrapper ovrd_type;
  function new (string full_inst_path="",
                string orig_type_name="",
                ovm_object_wrapper orig_type=null,
                ovm_object_wrapper ovrd_type);
    if (ovrd_type == null) begin
      ovm_report_fatal ("NULLWR", "Attempting to register a null override object with the factory", OVM_NONE);
    end
    this.full_inst_path= full_inst_path;
    this.orig_type_name = orig_type == null ? orig_type_name : orig_type.get_type_name();
    this.orig_type      = orig_type;
    this.ovrd_type_name = ovrd_type.get_type_name();
    this.ovrd_type      = ovrd_type;
  endfunction
endclass


//-----------------------------------------------------------------------------
// our singleton factory; it is statically initialized
//-----------------------------------------------------------------------------

`const ovm_factory factory = ovm_factory::get();

`endif // OVM_FACTORY_SVH
