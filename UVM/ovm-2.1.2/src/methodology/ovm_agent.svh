// $Id: //dvt/vtech/dev/main/ovm/src/methodology/ovm_agent.svh#6 $
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

`ifndef OVM_AGENT_SVH
`define OVM_AGENT_SVH

//------------------------------------------------------------------------------
//
// CLASS: ovm_agent
//
// The ovm_agent virtual class should be used as the base class for the user-
// defined agents. Deriving from ovm_agent will allow you to distinguish agents
// from other component types also using its inheritance. Such agents will
// automatically inherit features that may be added to ovm_agent in the future.
// 
// While an agent's build function, inherited from <ovm_component>, can be
// implemented to define any agent topology, an agent typically contains three
// subcomponents: a driver, sequencer, and monitor. If the agent is active,
// subtypes should contain all three subcomponents. If the agent is passive,
// subtypes should contain only the monitor.
//------------------------------------------------------------------------------

virtual class ovm_agent extends ovm_component;

  // Function: new
  //
  // Creates and initializes an instance of this class using the normal
  // constructor arguments for <ovm_component>: ~name~ is the name of the
  // instance, and ~parent~ is the handle to the hierarchical parent, if any.

  function new (string name, ovm_component parent);
    super.new(name, parent);
  endfunction

  const static string type_name = "ovm_agent";

  virtual function string get_type_name ();
    return type_name;
  endfunction

endclass

`endif // OVM_AGENT_SVH
