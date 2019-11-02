//----------------------------------------------------------------------
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
//----------------------------------------------------------------------


// This file pulls in only untemplated classes. This allows for the 
// untemplated base code to reside in a package. For simulators
// which do not fully support templated classes in packages, this
// allows the base classes to be shared by many scopes. The file
// ovm_templates.svh can be included in each scope that needs to use
// the templated classes.


`ifndef OVM_BASE_PKG_SV
`define OVM_BASE_PKG_SV

// the following indicates only the base layer is being brought in
`define OVM_BASE_ONLY

// the following indicates we are creating a package
`define OVM_PKG_SV

package ovm_pkg;

`ifdef USE_PARAMETERIZED_WRAPPER
  `include "ovm.svh"
`else
  `include "ovm_macros.svh"
  `include "base/base.svh"
  `include "methodology/methodology_noparm.svh"

// Include for backwards compatibility
  `include "compatibility/base_compatibility.svh"
`endif
endpackage


`endif


