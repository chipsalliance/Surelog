// $Id: ovm_config.sv,v 1.5 2009/10/30 15:29:21 jlrose Exp $
//----------------------------------------------------------------------
//   Copyright 2007-2008 Mentor Graphics Corporation
//   Copyright 2007-2008 Cadence Design Systems, Inc.
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

`include "base/ovm_config.svh"

typedef class ovm_root;

//----------------------------------------------------------------------
//
// ovm_config_setting implementation
//
//----------------------------------------------------------------------

function ovm_config_setting::new (string inst, string field, ovm_component from);
  this.m_inst = inst;
  this.m_field = field;
  this.m_from = from;
  foreach (inst[i]) begin
    if(inst[i] == "*" || inst[i] == "?") begin
      m_inst_wildcard = 1;
      break;
    end 
  end
  foreach (field[i]) begin
    if(field[i] == "*" || field[i] == "?") begin
      m_field_wildcard = 1;
      break;
    end 
  end
endfunction

function bit ovm_config_setting::component_match (ovm_component to);
  if(to==null) return 0;
  if(m_from == ovm_root::get() || m_from == null) begin
    if(!this.m_inst_wildcard)
      return m_inst == to.get_full_name();
    return ovm_is_match(m_inst, to.get_full_name());
  end
  else if (m_inst == "")
    return m_from == to;
  else begin
    if(!this.m_inst_wildcard)
      return {m_from.get_full_name(), ".", m_inst} == to.get_full_name();
    return ovm_is_match({m_from.get_full_name(), ".", m_inst}, to.get_full_name());
  end
endfunction

function bit ovm_config_setting::field_match (string to);
  if(to == "") return 0;
  if(!this.m_field_wildcard)
    return m_field == to;
  return ovm_is_match(m_field, to);
endfunction


function string ovm_config_setting::matches_string(ovm_component to, ovm_component from);
  string v;
  if(component_match(to)) begin
    if(from==ovm_root::get()) begin
      v = " GLOBAL"; while(v.len() < 17) v = {v, " "};
    end
    else begin
      $swrite(v, " %0s(%0s)",from.get_full_name(), from.get_type_name()); while(v.len() < 17) v = {v, " "};
    end
    if(from == ovm_root::get())
      v = {v, " ", m_inst};
    else
      v = {v, " ", from.get_full_name(), ".", m_inst}; 
    while(v.len() < 35) v = {v," "};
    v = {v, " ", m_field}; while(v.len() < 48) v = {v," "};
    return v;
  end
endfunction


function void ovm_config_setting::print_match (ovm_component to, 
                                               ovm_component from, 
                                               string field);
  if((to!=null) && from!=ovm_root::get() && from!=null)
    $display("Configuration match for %s.%s from %s: instance match = \"%s.%s\"  field match = \"%s\"",
      to.get_full_name(), field, from.get_full_name(), from.get_full_name(), m_inst, field);
  else if(to!=null)
    $display("Configuration match for %s.%s from %s: instance match = \"%s\"  field match = \"%s\"",
      to.get_full_name(), field, "GLOBAL", m_inst, field);
  else 
    $display("Configuration match for %s from %s: instance match = \"%s.%s\"  field match = \"%s\"",
      field, "GLOBAL", from.get_full_name(), m_inst, field);
endfunction

function void  ovm_config_setting::set_override (ovm_config_setting ov);
  m_override_list.push_back(ov);
endfunction

function void  ovm_config_setting::set_used (ovm_component      used);
  m_used_list.push_back(used);
endfunction

function string ovm_config_setting::convert2string ();
  convert2string = { type_string(), ": component=", m_inst, ", field=", 
    m_field, ", value=", value_string() };
endfunction

function ovm_component ovm_config_setting::get_from_component();
  return m_from;
endfunction

function void ovm_config_setting::get_to_list (ref ovm_component list[$]);
  while(list.size()) void'(list.pop_front());
  foreach(m_used_list[i]) list.push_back(m_used_list[i]);
endfunction

function void ovm_config_setting::get_override_list (ref ovm_config_setting list[$]);
  while(list.size()) void'(list.pop_front());
  foreach(m_override_list[i]) list.push_back(m_override_list[i]);
endfunction

function int ovm_config_setting::num_overrides ();
  return m_override_list.size();
endfunction

function int ovm_config_setting::num_used ();
  return m_used_list.size();
endfunction

function string ovm_config_setting::unused_message ();
  unused_message = { type_string(), ": \"", convert2string(), "\"", " from component "};
  if(m_from == ovm_root::get() || m_from == null)
    unused_message = { unused_message, "GLOBAL"};
  else
    unused_message = { unused_message, m_from.get_full_name()};
endfunction

function string ovm_config_setting::overridden_message();
  overridden_message = {unused_message(), ", overridden from component(s) : "};
  foreach(m_override_list[i])
    if(i==0)
      overridden_message = {overridden_message, m_override_list[i].m_from.get_full_name() };
     else
      overridden_message = {overridden_message, ", ", m_override_list[i].m_from.get_full_name() };
endfunction

function string ovm_config_setting::applied_message ();
  applied_message = {unused_message(), ", applied to component(s) : "};
  foreach(m_used_list[i])
    if(i==0)
      applied_message = {applied_message, m_used_list[i].get_full_name() };
    else
      applied_message = {applied_message, ", ", m_used_list[i].get_full_name() };
endfunction


function ovm_int_config_setting::new (string inst, 
                                      string field, 
                                      ovm_bitstream_t value, 
                                      ovm_component from);
  super.new(inst, field, from);
  this.m_value = value;
endfunction

function string ovm_int_config_setting::matches_string(ovm_component to, ovm_component from);
  if(component_match(to)) begin
    matches_string = super.matches_string(to, from);
    $swrite(matches_string, "%s int     %0d", matches_string, m_value);
  end
endfunction

function string ovm_int_config_setting::value_string();
  $swrite(value_string, "%0d", m_value);
endfunction

function string ovm_int_config_setting::type_string();
  return "Integral";
endfunction

function ovm_config_setting::ovm_config_type ovm_int_config_setting::get_value_type (); 
  return OVM_INT_TYPE;
endfunction

function ovm_string_config_setting::new (string inst, 
                                         string field, 
                                         string value, 
                                         ovm_component from);
  super.new(inst, field, from);
  this.m_value = value;
endfunction

function string ovm_string_config_setting::matches_string(ovm_component to, ovm_component from);
  if(component_match(to)) begin
    matches_string = super.matches_string(to, from);
    $swrite(matches_string, "%s string  %0s", matches_string, m_value);
  end
endfunction

function string ovm_string_config_setting::value_string();
  $swrite(value_string, "\"%0s\"", m_value);
endfunction

function string ovm_string_config_setting::type_string();
  return "String";
endfunction

function ovm_config_setting::ovm_config_type ovm_string_config_setting::get_value_type (); 
  return OVM_STRING_TYPE;
endfunction

function ovm_object_config_setting::new (string        inst, 
                                         string        field, 
                                         ovm_object    value, 
                                         ovm_component from, 
                                         bit           clone);
  super.new(inst, field, from);
  this.m_value = value;
  this.m_clone = clone;
endfunction

function string ovm_object_config_setting::matches_string(ovm_component to, ovm_component from);
  string s2;
  if(component_match(to)) begin
    s2 = ovm_object_value_str(m_value);
    matches_string = super.matches_string(to, from);
    $swrite(matches_string, "%s %0s  %0s", matches_string, type_string(), s2);
  end
endfunction

function string ovm_object_config_setting::value_string();
`ifdef INCA
  $swrite(value_string, "@%0d", m_value);
`else
  return "<object handle>";
`endif
endfunction

function string ovm_object_config_setting::type_string();
  if(m_value == null) return "Object";
  else return m_value.get_type_name();
endfunction

function ovm_config_setting::ovm_config_type ovm_object_config_setting::get_value_type (); 
  return OVM_OBJECT_TYPE;
endfunction

