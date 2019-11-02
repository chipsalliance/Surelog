// $Id: //dvt/vtech/dev/main/ovm/src/compatibility/urm_type_compatibility.svh#11 $
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
`ifndef URM_TYPE_COMPATIBILITY_SVH
`define URM_TYPE_COMPATIBILITY_SVH

typedef ovm_object             urm_object;
typedef ovm_transaction        urm_transaction;
typedef ovm_event              urm_event;
typedef ovm_event_pool         urm_event_pool;
typedef ovm_component          urm_named_object;
typedef ovm_component          urm_unit_base;
typedef ovm_component          urm_unit;
typedef ovm_printer            urm_printer;
typedef ovm_comparer           urm_comparer;
typedef ovm_recorder           urm_recorder;
typedef ovm_factory            urm_factory;
typedef ovm_object_wrapper     urm_object_wrapper;

`ifdef URM_GLOBALS

parameter NONE = int'(OVM_NONE);
parameter LOW = int'(OVM_LOW);
parameter MEDIUM = int'(OVM_MEDIUM);
parameter HIGH = int'(OVM_HIGH);
parameter FULL = int'(OVM_FULL);
parameter STREAMBITS = int'(OVM_STREAMBITS);
parameter RADIX = int'(OVM_RADIX);
parameter BIN = int'(OVM_BIN);
parameter DEC = int'(OVM_DEC);
parameter UNSIGNED = int'(OVM_UNSIGNED);
parameter OCT = int'(OVM_OCT);
parameter HEX = int'(OVM_HEX);
parameter STRING = int'(OVM_STRING);
parameter TIME = int'(OVM_TIME);
parameter ENUM = int'(OVM_ENUM);
parameter NORADIX = int'(OVM_NORADIX);
parameter DEFAULT_POLICY = int'(OVM_DEFAULT_POLICY);
parameter DEEP = int'(OVM_DEEP);
parameter SHALLOW = int'(OVM_SHALLOW);
parameter REFERENCE = int'(OVM_REFERENCE);
parameter DEFAULT = int'(OVM_DEFAULT);
parameter ALL_ON = int'(OVM_ALL_ON);
parameter COPY = int'(OVM_COPY);
parameter NOCOPY = int'(OVM_NOCOPY);
parameter COMPARE = int'(OVM_COMPARE);
parameter NOCOMPARE = int'(OVM_NOCOMPARE);
parameter PRINT = int'(OVM_PRINT);
parameter NOPRINT = int'(OVM_NOPRINT);
parameter RECORD = int'(OVM_RECORD);
parameter NORECORD = int'(OVM_NORECORD);
parameter PACK = int'(OVM_PACK);
parameter NOPACK = int'(OVM_NOPACK);
parameter PHYSICAL = int'(OVM_PHYSICAL);
parameter ABSTRACT = int'(OVM_ABSTRACT);
parameter READONLY = int'(OVM_READONLY);
parameter NODEFPRINT = int'(OVM_NODEFPRINT);

typedef ovm_radix_enum radix_enum;
typedef ovm_bitstream_t bitstream_t;

function void print_topology();
   ovm_print_topology();
endfunction
function bit is_match(string e, string m);
  return ovm_is_match(e,m);
endfunction
function logic[OVM_LARGE_STRING:0] string_to_bits(string str);
  return ovm_string_to_bits(str);
endfunction
function string bits_to_string(logic[OVM_LARGE_STRING:0] str);
  return ovm_bits_to_string(str);
endfunction
function ovm_component get_unit(string name);
  return ovm_top.find(name);
endfunction
function automatic void get_units(string name, ref urm_unit_base cq[$]);
  ovm_top.find_all(name, cq);
endfunction

ovm_printer default_printer = ovm_default_printer;
ovm_tree_printer default_tree_printer = ovm_default_tree_printer;
ovm_line_printer default_line_printer = ovm_default_line_printer;
ovm_table_printer default_table_printer = ovm_default_table_printer;

`endif

`endif
