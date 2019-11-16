// $Id: //dvt/vtech/dev/main/ovm/src/compatibility/urm_macro_compatibility.svh#8 $
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
`ifndef BACKWARD_COMPAT_MACROS_SVH
`define BACKWARD_COMPAT_MACROS_SVH

`define urm_object_utils(T)                 `ovm_object_utils(T)
`define urm_object_utils_begin(T)           `ovm_object_utils_begin(T)
`define urm_object_utils_end                `ovm_object_utils_end
`define urm_field_utils(T)                  `ovm_field_utils(T)
`define urm_field_utils_begin(T)            `ovm_field_utils_begin(T)
`define urm_field_utils_end                 `ovm_field_utils_end

`define urm_component_factory_create_func(T) \
   function ovm_component create_component (string name, ovm_component parent); \
     T tmp; \
     urm_unit p; \
     $cast(p, parent); \
     tmp = new(.name(name), .parent(p)); \
     return tmp; \
   endfunction

`define urm_unit_wrapper_derived_class(T) \
   class T``wrapper extends ovm_object_wrapper; \
     virtual function string get_type_name (); \
       return `"T`"; \
     endfunction \
     `urm_component_factory_create_func(T) \
   endclass

`define urm_unit_utils_begin(T) \
   `urm_unit_wrapper_derived_class(T)  \
   `ovm_component_registry_internal(T,T) \
   `ovm_get_type_name_func(T) \
   `ovm_field_utils_begin(T)

`define urm_unit_utils(T) \
  `urm_unit_utils_begin(T) \
  `urm_unit_utils_end

`define urm_unit_utils_end                  `ovm_component_utils_end
`define urm_unit_base_utils(T)              `urm_unit_utils(T)
`define urm_unit_base_utils_begin(T)        `urm_unit_utils_begin(T)
`define urm_unit_base_utils_end             `urm_unit_utils_end

`define urm_field_int(F, FL)              `ovm_field_int(F, FL)
`define urm_field_object(F, FL)           `ovm_field_object(F, FL)
`define urm_field_event(F, FL)            `ovm_field_event(F, FL)
`define urm_field_string(F, FL)           `ovm_field_string(F, FL)
`define urm_field_array_int(F, FL)        `ovm_field_array_int(F, FL)
`define urm_field_array_object(F, FL)     `ovm_field_array_object(F, FL)
`define urm_field_array_string(F, FL)     `ovm_field_array_string(F, FL)
`define urm_field_queue_int(F, FL)        `ovm_field_queue_int(F, FL)
`define urm_field_queue_object(F, FL)     `ovm_field_queue_object(F, FL)
`define urm_field_queue_string(F, FL)     `ovm_field_queue_string(F, FL)
`define urm_field_aa_int_string(F, FL)    `ovm_field_aa_int_string(F, FL)
`define urm_field_aa_object_string(F, FL) `ovm_field_aa_object_string(F, FL)
`define urm_field_aa_string_string(F, FL) `ovm_field_aa_string_string(F, FL)
`define urm_field_aa_object_int(F, FL)    `ovm_field_aa_object_int(F, FL)
`define urm_field_aa_int_int(F, FL)       `ovm_field_aa_int_int(F, FL)
`define urm_field_aa_int_int_unsigned(F, FL)      `ovm_field_aa_int_int_unsigned(F, FL)
`define urm_field_aa_int_integer(F, FL)           `ovm_field_aa_int_integer(F, FL)
`define urm_field_aa_int_integer_unsigned(F, FL)  `ovm_field_aa_int_integer_unsigned(F, FL)
`define urm_field_aa_int_byte(F, FL)              `ovm_field_aa_int_byte(F, FL)
`define urm_field_aa_int_byte_unsigned(F, FL)     `ovm_field_aa_int_byte_unsigned(F, FL)
`define urm_field_aa_int_shortint(F, FL)          `ovm_field_aa_int_shortint(F, FL)
`define urm_field_aa_int_shortint_unsigned(F, FL) `ovm_field_aa_int_shortint_unsigned(F, FL)
`define urm_field_aa_int_longint(F, FL)           `ovm_field_aa_int_longint(F, FL)
`define urm_field_aa_int_longint_unsigned(F, FL)  `ovm_field_aa_int_longint_unsigned(F, FL)
`define urm_field_aa_int_key(F, FL)               `ovm_field_aa_int_key(F, FL)
`define ovm_msg_detail(L)                   `urm_msg_detail(L)

`endif
