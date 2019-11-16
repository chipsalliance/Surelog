// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_misc.svh#21 $
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

`ifndef OVM_MISC_SVH
`define OVM_MISC_SVH

// Used to indicate "no valid default value" in a parameter
virtual class avm_virtual_class; endclass

//------------------------------------------------------------------------------
//
// Topic: ovm_void
//
// The ~ovm_void~ class is the base class for all OVM classes. It is an abstract
// class with no data members or functions. It allows for generic containers of
// objects to be created, similar to a void pointer in the C programming
// language. User classes derived directly from ~ovm_void~ inherit none of the
// OVM functionality, but such classes may be placed in ~ovm_void~-typed
// containers along with other OVM objects.
//
//------------------------------------------------------------------------------

virtual class ovm_void;
endclass

// Forward declaration since scope stack uses ovm_objects now
typedef class ovm_object;

//----------------------------------------------------------------------------
//
// CLASS- ovm_scope_stack
//
//----------------------------------------------------------------------------

class ovm_scope_stack;
  local string   m_scope="";
  local string   m_scope_arg="";
  local int      m_depth=0;
  local bit      m_object_map[ovm_void];
  local ovm_void m_stack[$];

  extern function void   set          (string s, ovm_object obj);
  extern function void   down         (string s, ovm_object obj);
  extern function void   down_element (int element, ovm_object obj);
  extern function void   up           (ovm_object obj, byte separator=".");
  extern function void   up_element   (ovm_object obj);
  extern function void   set_arg      (string arg);
  extern function void   unset_arg    (string arg);
  extern function void   set_arg_element  (string arg, int ele);
  extern function int    depth        ();
  extern function string get          ();
  extern function string get_arg      ();
  extern function ovm_object current    ();

  extern function bit    in_hierarchy  (ovm_object obj);
endclass

`endif // OVM_MISC_SVH
