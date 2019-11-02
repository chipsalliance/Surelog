// $Id: //dvt/vtech/dev/main/ovm/src/methodology/ovm_subscriber.svh#7 $
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

//------------------------------------------------------------------------------
//
// CLASS: ovm_subscriber
//
// This class provides an analysis export for receiving transactions from a
// connected analysis export. Making such a connection "subscribes" this
// component to any transactions emitted by the connected analysis port.
//
// Subtypes of this class must define the write method to process the incoming
// transactions. This class is particularly useful when designing a coverage
// collector that attaches to a monitor. 
//------------------------------------------------------------------------------

virtual class ovm_subscriber #(type T=int) extends ovm_component;

  typedef ovm_subscriber #(T) this_type;

  // Port: analysis_export
  //
  // This export provides access to the write method, which derived subscribers
  // must implement.

  ovm_analysis_imp #(T, this_type) analysis_export;
  
  // Function: new
  //
  // Creates and initializes an instance of this class using the normal
  // constructor arguments for <ovm_component>: ~name~ is the name of the
  // instance, and ~parent~ is the handle to the hierarchical parent, if any.

  function new (string name, ovm_component parent);
    super.new(name, parent);
    analysis_export = new("analysis_imp", this);
  endfunction
  
  // Function: write
  //
  // A pure virtual method that must be defined in each subclass. Access
  // to this method by outside components should be done via the
  // analysis_export.

  pure virtual function void write(T t);
    
endclass

