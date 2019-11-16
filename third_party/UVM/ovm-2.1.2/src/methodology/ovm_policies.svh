// $Id: //dvt/vtech/dev/main/ovm/src/methodology/ovm_policies.svh#7 $
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

`ifndef OVM_POLICIES_SVH
`define OVM_POLICIES_SVH


// Group: Policy Classes
//
// Policy classes are used to implement polymorphic operations that
// differ between built-in types and class-based types. Generic
// components can then be built that work with either classes or 
// built-in types, depending on what policy class is used.


//----------------------------------------------------------------------
// CLASS: ovm_built_in_comp #(T)
// 
// This policy class is used to compare built-in types.
//
// Provides a comp method that compares, AVM-style, the built-in type,
// T, for which the == operator is defined.
//----------------------------------------------------------------------

class ovm_built_in_comp #(type T=int);

  static function bit comp(T a, T b);
    return a == b;
  endfunction

endclass


//----------------------------------------------------------------------
// CLASS: ovm_built_in_converter #(T)
//
// This policy class is used to convert built-in types to strings.
//
// Provides a convert2string method that converts the built-in type, T,
// to a string using the %p format specifier.
//----------------------------------------------------------------------

class ovm_built_in_converter #(type T=int);

  static function string convert2string(input T t);
    string s;
`ifdef INCA
    $swrite(s, t);
`else
    $sformat( s , "%p" , t );
`endif
    return s; 
  endfunction

endclass


//----------------------------------------------------------------------
// CLASS: ovm_built_in_clone #(T)
//
// This policy class is used to clone built-in types via the = operator.
//
// Provides a clone metod that returns a copy of the built-in type, T.
//----------------------------------------------------------------------

class ovm_built_in_clone #(type T=int);

  static function T clone(input T from);
    return from;
  endfunction

endclass


//----------------------------------------------------------------------
// CLASS: ovm_class_comp #(T)
//
// This policy class is used to compare two objects of the same type.
//
// Provides a comp method that compares two objects of type T. The
// class T must implement the comp method, to which this class delegates
// the operation.
//----------------------------------------------------------------------

class ovm_class_comp #(type T=int);

  static function bit comp(input T a, input T b);
    return a.comp(b);
  endfunction

endclass


//----------------------------------------------------------------------
// CLASS: ovm_class_converter #(T)
//
// This policy class is used to convert a class object to a string.
//
// Provides a convert2string method that converts the built-in type, T,
// to a string. The class T must implement the convert2string method,
// to which this class delegates the operation.
//----------------------------------------------------------------------

class ovm_class_converter #(type T=int);

  static function string convert2string(input T t);
    return t.convert2string();
  endfunction

endclass


//----------------------------------------------------------------------
// CLASS: ovm_class_clone #(T)
//
// This policy class is used to clone class objects.
//
// Provides a clone metod that returns a copy of the built-in type, T.
// The class T must implement the clone method, to which this class
// delegates the operation.
//----------------------------------------------------------------------

class ovm_class_clone #(type T=int);

  static function ovm_object clone(input T from);
    return from.clone();
  endfunction

endclass

`endif // OVM_POLICIES_SVH

