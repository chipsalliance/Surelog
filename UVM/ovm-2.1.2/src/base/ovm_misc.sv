// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_misc.sv#19 $
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

`include "base/ovm_misc.svh"

// Create a seed which is based off of the ius seed which can be used to seed
// srandom processes but will change if the command line seed setting is 
// changed.

int unsigned ovm_global_random_seed = $urandom;

// This map is a seed map that can be used to update seeds. The update
// is done automatically by the seed hashing routine. The seed_table_lookup
// uses an instance name lookup and the seed_table inside a given map
// uses a type name for the lookup.

class ovm_seed_map;
  int unsigned seed_table [string];
  int unsigned count [string];
endclass
ovm_seed_map ovm_random_seed_table_lookup [string];

//
// ovm_instance_scope;
//
// A function that returns the scope that the urm library lives in, either
// an instance, a module, or a package.

function string ovm_instance_scope();
  byte c;
  int pos;
  //first time through the scope is null and we need to calculate, afterwards it
  //is correctly set.

  if(ovm_instance_scope != "") 
    return ovm_instance_scope;

  $swrite(ovm_instance_scope, "%m");
  //remove the extraneous .ovm_instance_scope piece or ::ovm_instance_scope
  pos = ovm_instance_scope.len()-1;
  c = ovm_instance_scope[pos];
  while(pos && (c != ".") && (c != ":")) 
    c = ovm_instance_scope[--pos];
  if(pos == 0)
    ovm_report_error("SCPSTR", $psprintf("Illegal name %s in scope string",ovm_instance_scope));
  ovm_instance_scope = ovm_instance_scope.substr(0,pos);
endfunction


//
// ovm_oneway_hash
//
// A one-way hash function that is useful for creating srandom seeds. An
// unsigned int value is generated from the string input. An initial seed can
// be used to seed the hash, if not supplied the ovm_global_random_seed 
// value is used. Uses a CRC like functionality to minimize collisions.

parameter OVM_STR_CRC_POLYNOMIAL = 32'h04c11db6;
function int unsigned ovm_oneway_hash ( string string_in, int unsigned seed=0 );
  bit          msb;
  bit [7:0]    current_byte;
  bit [31:0]   crc1;
      
  if(!seed) seed = ovm_global_random_seed;
  ovm_oneway_hash = seed;

  crc1 = 32'hffffffff;
  for (int _byte=0; _byte < string_in.len(); _byte++) begin
     current_byte = string_in[_byte];
     if (current_byte == 0) break;
     for (int _bit=0; _bit < 8; _bit++) begin
        msb = crc1[31];
        crc1 <<= 1;
        if (msb ^ current_byte[_bit]) begin
           crc1 ^=  OVM_STR_CRC_POLYNOMIAL;
           crc1[0] = 1;
        end
     end
  end
  ovm_oneway_hash += ~{crc1[7:0], crc1[15:8], crc1[23:16], crc1[31:24]};

endfunction

//
// ovm_create_random_seed
//
// Creates a random seed and updates the seed map so that if the same string
// is used again, a new value will be generated. The inst_id is used to hash
// by instance name and get a map of type name hashes which the type_id uses
// for it's lookup.

function int unsigned ovm_create_random_seed ( string type_id, string inst_id="" );
  ovm_seed_map seed_map;

  if(inst_id == "")
    inst_id = "__global__";

  if(!ovm_random_seed_table_lookup.exists(inst_id))
    ovm_random_seed_table_lookup[inst_id] = new;
  seed_map = ovm_random_seed_table_lookup[inst_id];

  type_id = {ovm_instance_scope(),type_id};

  if(!seed_map.seed_table.exists(type_id)) begin
    seed_map.seed_table[type_id] = ovm_oneway_hash ({type_id,"::",inst_id}, ovm_global_random_seed);
  end
  if (!seed_map.count.exists(type_id)) begin
    seed_map.count[type_id] = 0;
  end

  //can't just increment, otherwise too much chance for collision, so 
  //randomize the seed using the last seed as the seed value. Check if
  //the seed has been used before and if so increment it.
  seed_map.seed_table[type_id] = seed_map.seed_table[type_id]+seed_map.count[type_id]; 
  seed_map.count[type_id]++;

  return seed_map.seed_table[type_id];
endfunction


//----------------------------------------------------------------------------
//
// CLASS- ovm_scope_stack
//
//----------------------------------------------------------------------------

// depth
// -----

function int ovm_scope_stack::depth();
  return m_stack.size();
endfunction


// scope
// -----

function string ovm_scope_stack::get();
  return m_scope;
endfunction


// scope_arg
// ---------

function string ovm_scope_stack::get_arg();
  return m_scope_arg;
endfunction


// set_scope
// ---------

function void ovm_scope_stack::set (string s, ovm_object obj);
  ovm_void v; v=obj;
  m_scope_arg = s;
  m_scope = s;

  // When no arg delete() is supported for queues, can just call m_stack.delete().
  while(m_stack.size()) void'(m_stack.pop_front());
  
  m_stack.push_back(v);
  if(v!=null) begin
   m_object_map[v] = 1;
  end
endfunction


// down
// ----

function void ovm_scope_stack::down (string s, ovm_object obj);
  ovm_void v; v=obj;
  if(m_scope == "")
    m_scope = s;
  else if(s.len()) begin
    if(s[0] == "[")
      m_scope = {m_scope,s};
    else
      m_scope = {m_scope,".",s};
  end
  m_scope_arg=m_scope;
  if(v!=null) begin
    m_object_map[v] = 1;
  end
  m_stack.push_back(v);
endfunction


// down_element
// ------------

function void ovm_scope_stack::down_element (int element, ovm_object obj);
  string tmp_value_str;
  ovm_void v; v=obj;
  tmp_value_str.itoa(element);

  m_scope = {m_scope, "[", tmp_value_str, "]"};
  m_scope_arg=m_scope;
  m_stack.push_back(v);
  if(v!=null)
    m_object_map[v] = 1;
endfunction

// current
// -------

function ovm_object ovm_scope_stack::current ();
  ovm_void v;
  if(m_stack.size()) begin
    v = m_stack[m_stack.size()-1];
    $cast(current, v);
  end
  else
    return null;
endfunction

// up
// --

function void ovm_scope_stack::up (ovm_object obj, byte separator =".");
  string tmp_value_str;
  int last_dot;
  if(!m_scope.len()) begin
    // When no arg delete() is supported for associative arrays, can just call 
    // m_object_map.delete().
    foreach(m_object_map[i]) m_object_map.delete(i);
    // When no arg delete() is supported for queues, can just call m_stack.delete().
    while(m_stack.size()) void'(m_stack.pop_front());
    return;
  end
  //Find the last scope separator
  for(last_dot = m_scope.len()-1; last_dot != 0; --last_dot)
    if(m_scope[last_dot] == separator) break;

  if(!last_dot)
    m_scope = "";

  tmp_value_str = "";
  for(int i=0; i<last_dot; ++i) begin
    tmp_value_str = {tmp_value_str, " "};
    tmp_value_str[i] = m_scope[i];
  end
  m_scope = tmp_value_str;
  void'(m_stack.pop_back());
  if(m_stack.size() == 0)
    m_scope = "";

  m_scope_arg = m_scope;
  m_object_map.delete(obj);
endfunction


// up_element
// ----------

function void ovm_scope_stack::up_element (ovm_object obj);
  up(obj, "[");
endfunction


// set_arg
// -------

function void ovm_scope_stack::set_arg (string arg);
  if(m_scope == "")
    m_scope_arg = arg;
  else if(arg[0] == "[")
    m_scope_arg = {m_scope, arg};
  else 
    m_scope_arg = {m_scope, ".", arg};
endfunction


// set_arg_element
// ---------------

function void ovm_scope_stack::set_arg_element (string arg, int ele);
  string tmp_value_str;
  tmp_value_str.itoa(ele);
  if(m_scope == "")
    m_scope_arg = {arg, "[", tmp_value_str, "]"};
  else
    m_scope_arg = {m_scope, ".", arg, "[", tmp_value_str, "]"};
endfunction

function void ovm_scope_stack::unset_arg (string arg);
  int s, sa;

  if((arg.len() == 0) || (m_scope_arg.len() == 0))
    return;

  s=m_scope_arg.len() - 1;
  sa=arg.len() - 1;

  if(m_scope_arg[s] == "]" && arg[sa] != "]") 
    s--;
  if(s<sa) return;
  while(sa>=0 && s >= 0) begin
    if(m_scope_arg[s] != arg[sa]) return;
    s--; sa--;
  end
  if(s>=0 && m_scope_arg[s] == ".") 
    s--;
  else if(s > 0 && m_scope_arg[s] == "[" && m_scope_arg[m_scope_arg.len()-1]=="]")
    s--;
  m_scope_arg = m_scope_arg.substr(0,s);
endfunction

// in_hierarchy
// ------------

function bit ovm_scope_stack::in_hierarchy (ovm_object obj);
  ovm_void v; v = obj;
  if (!m_object_map.exists(v)) return 0;
  return m_object_map[v];
endfunction

// ovm_leaf_scope
// --------------
function string ovm_leaf_scope (string full_name, byte scope_separator = ".");
  byte bracket_match;
  int  pos;
  int  bmatches;

  bmatches = 0;
  case(scope_separator)
    "[": bracket_match = "]";
    "(": bracket_match = ")";
    "<": bracket_match = ">";
    "{": bracket_match = "}";
    default: bracket_match = "";
  endcase

  //Only use bracket matching if the input string has the end match
  if(bracket_match != "" && bracket_match != full_name[full_name.len()-1])
    bracket_match = "";

  for(pos=full_name.len()-1; pos!=0; --pos) begin
    if(full_name[pos] == bracket_match) bmatches++;
    else if(full_name[pos] == scope_separator) begin
      bmatches--;
      if(!bmatches || (bracket_match == "")) break;
    end
  end
  if(pos) begin
    if(scope_separator != ".") pos--;
    ovm_leaf_scope = full_name.substr(pos+1,full_name.len()-1);
  end
  else begin
    ovm_leaf_scope = full_name;
  end
endfunction


// OVM does not provide any kind of recording functionality, but provides hooks
// when a component/object may need such a hook.


`ifndef OVM_RECORD_INTERFACE
`define OVM_RECORD_INTERFACE

// ovm_create_fiber
// ----------------

function integer ovm_create_fiber (string name,
                                   string t,
                                   string scope);
  return 0;
endfunction

// ovm_set_index_attribute_by_name
// -------------------------------

function void ovm_set_index_attribute_by_name (integer txh,
                                         string nm,
                                         int index,
                                         logic [1023:0] value,
                                         string radix,
                                         integer numbits=32);
  return;
endfunction


// ovm_set_attribute_by_name
// -------------------------

function void ovm_set_attribute_by_name (integer txh,
                                         string nm,
                                         logic [1023:0] value,
                                         string radix,
                                         integer numbits=0);
  return;
endfunction


// ovm_check_handle_kind
// ---------------------

function integer ovm_check_handle_kind (string htype, integer handle);
  return 1;
endfunction


// ovm_begin_transaction
// ---------------

function integer ovm_begin_transaction(string txtype,
                                 integer stream,
                                 string nm
                                 , string label="",
                                 string desc="",
                                 time begin_time=0
                                 );

  return 0;
endfunction


// ovm_end_transaction
// -------------------

function void ovm_end_transaction (integer handle
                                 , time end_time=0
);
  return;
endfunction


// ovm_link_transaction
// --------------------

function void ovm_link_transaction(integer h1, integer h2,
                                   string relation="");
  return;
endfunction



// ovm_free_transaction_handle
// ---------------------------

function void ovm_free_transaction_handle(integer handle);
  return;
endfunction

`endif // OVM_RECORD_INTERFACE

// The following functions check to see if a string is representing an array
// index, and if so, what the index is.

function int ovm_get_array_index_int(string arg, output bit is_wildcard);
  int i;
  ovm_get_array_index_int = 0;
  is_wildcard = 1;
  i = arg.len() - 1;
  if(arg[i] == "]")
    while(i > 0 && (arg[i] != "[")) begin
      --i;
      if((arg[i] == "*") || (arg[i] == "?")) i=0;
      else if((arg[i] < "0") || (arg[i] > "9") && (arg[i] != "[")) begin
        ovm_get_array_index_int = -1; //illegal integral index
        i=0;
      end
    end
  else begin
    is_wildcard = 0;
    return 0;
  end

  if(i>0) begin
    arg = arg.substr(i+1, arg.len()-2);
    ovm_get_array_index_int = arg.atoi(); 
    is_wildcard = 0;
  end
endfunction 
  
function string ovm_get_array_index_string(string arg, output bit is_wildcard);
  int i;
  ovm_get_array_index_string = "";
  is_wildcard = 1;
  i = arg.len() - 1;
  if(arg[i] == "]")
    while(i > 0 && (arg[i] != "[")) begin
      if((arg[i] == "*") || (arg[i] == "?")) i=0;
      --i;
    end
  if(i>0) begin
    ovm_get_array_index_string = arg.substr(i+1, arg.len()-2);
    is_wildcard = 0;
  end
endfunction

function bit ovm_is_array(string arg);
  int last;
  ovm_is_array = 0;
  last = arg.len()-1;
  if(arg[last] == "]") ovm_is_array = 1;
endfunction


