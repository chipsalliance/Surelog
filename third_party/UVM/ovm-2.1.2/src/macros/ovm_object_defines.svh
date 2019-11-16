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

`ifndef OVM_OBJECT_DEFINES_SVH
`define OVM_OBJECT_DEFINES_SVH

`ifdef OVM_EMPTY_MACROS

`define ovm_field_utils
`define ovm_field_utils_begin(T) 
`define ovm_field_utils_end 
`define ovm_object_utils(T) 
`define ovm_object_param_utils(T) 
`define ovm_object_utils_begin(T) 
`define ovm_object_param_utils_begin(T) 
`define ovm_object_utils_end
`define ovm_component_utils(T)
`define ovm_component_param_utils(T)
`define ovm_component_utils_begin(T)
`define ovm_component_param_utils_begin(T)
`define ovm_component_utils_end
`define ovm_field_int(ARG,FLAG)
`define ovm_field_real(ARG,FLAG)
`define ovm_field_enum(T,ARG,FLAG)
`define ovm_field_object(ARG,FLAG)
`define ovm_field_event(ARG,FLAG)
`define ovm_field_string(ARG,FLAG)
`define ovm_field_array_enum(ARG,FLAG)
`define ovm_field_array_int(ARG,FLAG)
`define ovm_field_sarray_int(ARG,FLAG)
`define ovm_field_sarray_enum(ARG,FLAG)
`define ovm_field_array_object(ARG,FLAG)
`define ovm_field_sarray_object(ARG,FLAG)
`define ovm_field_array_string(ARG,FLAG)
`define ovm_field_sarray_string(ARG,FLAG)
`define ovm_field_queue_enum(ARG,FLAG)
`define ovm_field_queue_int(ARG,FLAG)
`define ovm_field_queue_object(ARG,FLAG)
`define ovm_field_queue_string(ARG,FLAG)
`define ovm_field_aa_int_string(ARG, FLAG)
`define ovm_field_aa_string_string(ARG, FLAG)
`define ovm_field_aa_object_string(ARG, FLAG)
`define ovm_field_aa_int_int(ARG, FLAG)
`define ovm_field_aa_int_int(ARG, FLAG)
`define ovm_field_aa_int_int_unsigned(ARG, FLAG)
`define ovm_field_aa_int_integer(ARG, FLAG)
`define ovm_field_aa_int_integer_unsigned(ARG, FLAG)
`define ovm_field_aa_int_byte(ARG, FLAG)
`define ovm_field_aa_int_byte_unsigned(ARG, FLAG)
`define ovm_field_aa_int_shortint(ARG, FLAG)
`define ovm_field_aa_int_shortint_unsigned(ARG, FLAG)
`define ovm_field_aa_int_longint(ARG, FLAG)
`define ovm_field_aa_int_longint_unsigned(ARG, FLAG)
`define ovm_field_aa_int_key(KEY, ARG, FLAG)
`define ovm_field_aa_string_int(ARG, FLAG)
`define ovm_field_aa_object_int(ARG, FLAG)

`else

//------------------------------------------------------------------------------
//
// Title: Utility and Field Macros for Components and Objects
//
// Group: Utility Macros 
//
// The utility macros provide implementations of the <ovm_object::create> method,
// which is needed for cloning, and the <ovm_object::get_type_name> method, which
// is needed for a number of debugging features. They also register the type with
// the <ovm_factory>, and they implement a ~get_type~ method, which is used when
// configuring the factory. And they implement the virtual 
// <ovm_object::get_object_type> method for accessing the factory proxy of an
// allocated object.
//
// Below is an example usage of the utility and field macros. By using the
// macros, you do not have to implement any of the data methods to get all of
// the capabilities of an <ovm_object>.
//
//|  class mydata extends ovm_object;
//| 
//|    string str;
//|    mydata subdata;
//|    int field;
//|    myenum e1;
//|    int queue[$];
//|
//|    `ovm_object_utils_begin(mydata) //requires ctor with default args
//|      `ovm_field_string(str, OVM_DEFAULT)
//|      `ovm_field_object(subdata, OVM_DEFAULT)
//|      `ovm_field_int(field, OVM_DEC) //use decimal radix
//|      `ovm_field_enum(myenum, e1, OVM_DEFAULT)
//|      `ovm_field_queue_int(queue, OVM_DEFAULT)
//|    `ovm_object_utils_end
//|
//|  endclass
//
//------------------------------------------------------------------------------

// Definitions for the user to use inside their derived data class declarations.

// MACRO: `ovm_field_utils_begin

// MACRO: `ovm_field_utils_end
//
// These macros form a block in which `ovm_field_* macros can be placed. 
// Used as
//
//|  `ovm_field_utils_begin(TYPE)
//|    `ovm_field_* macros here
//|  `ovm_field_utils_end
//
// 
// These macros do NOT perform factory registration, implement get_type_name,
// nor implement the create method. Use this form when you need custom
// implementations of these two methods, or when you are setting up field macros
// for an abstract class (i.e. virtual class).

`define ovm_field_utils_begin(T) \
   static bit m_fields_checked = 0; \
   function void m_field_automation (ovm_object tmp_data__, \
                                     int what__, \
                                     string str__); \
   begin \
     T local_data__; /* Used for copy and compare */ \
     typedef T ___local_type____; \
     string string_aa_key; /* Used for associative array lookups */ \
     /* Check the fields if not already checked */ \
     if(what__ == OVM_CHECK_FIELDS) begin \
       if(! ___local_type____``::m_fields_checked) \
         ___local_type____``::m_fields_checked=1; \
       else \
         return; \
     end \
     if(ovm_auto_options_object.recorder != null) begin \
       ovm_auto_options_object.recorder.scope = m_sc.scope; \
     end \
     /* Type is verified by ovm_object::compare() */ \
     super.m_field_automation(tmp_data__, what__, str__); \
     if(tmp_data__ != null) \
       /* Allow objects in same hierarchy to be copied/compared */ \
       if(!$cast(local_data__, tmp_data__)) return; \
     if(what__ == OVM_CHECK_FIELDS) begin \
       super.m_delete_field_array(); \
     end

`define ovm_field_utils_end \
     end \
   endfunction \

`define ovm_field_utils

// MACRO: `ovm_object_utils

// MACRO: `ovm_object_param_utils

// MACRO: `ovm_object_utils_begin

// MACRO: `ovm_object_param_utils_begin

// MACRO: `ovm_object_utils_end
//
// <ovm_object>-based class declarations may contain one of the above forms of
// utility macros.
// 
// For simple objects with no field macros, use
//
//|  `ovm_object_utils(TYPE)
//    
// For simple objects with field macros, use
//
//|  `ovm_object_utils_begin(TYPE)
//|    `ovm_field_* macro invocations here
//|  `ovm_object_utils_end
//    
// For parameterized objects with no field macros, use
//
//|  `ovm_object_param_utils(TYPE)
//    
// For parameterized objects, with field macros, use
//
//|  `ovm_object_param_utils_begin(TYPE)
//|    `ovm_field_* macro invocations here
//|  `ovm_object_utils_end
//
// Simple (non-parameterized) objects use the ovm_object_utils* versions, which
// do the following:
//
// o Implements get_type_name, which returns TYPE as a string
//
// o Implements create, which allocates an object of type TYPE by calling its
//   constructor with no arguments. TYPE's constructor, if defined, must have
//   default values on all it arguments.
//
// o Registers the TYPE with the factory, using the string TYPE as the factory
//   lookup string for the type.
//
// o Implements the static get_type() method which returns a factory
//   proxy object for the type.
//
// o Implements the virtual get_object_type() method which works just like the
//   static get_type() method, but operates on an already allocated object.
//
// Parameterized classes must use the ovm_object_param_utils* versions. They
// differ from <`ovm_object_utils> only in that they do not supply a type name
// when registering the object with the factory. As such, name-based lookup with
// the factory for parameterized classes is not possible.
//
// The macros with _begin suffixes are the same as the non-suffixed versions
// except that they also start a block in which `ovm_field_* macros can be
// placed. The block must be terminated by `ovm_object_utils_end.
//
// Objects deriving from ovm_sequence must use the `ovm_sequence_* macros
// instead of these macros.  See <`ovm_sequence_utils> for details.

`define ovm_object_utils(T) \
  `ovm_object_utils_begin(T) \
  `ovm_object_utils_end

`define ovm_object_param_utils(T) \
  `ovm_object_param_utils_begin(T) \
  `ovm_object_utils_end

`define ovm_object_utils_begin(T) \
   `ovm_object_registry_internal(T,T)  \
   `ovm_object_create_func(T) \
   `ovm_get_type_name_func(T) \
   `ovm_field_utils_begin(T) 

`define ovm_object_param_utils_begin(T) \
   `ovm_object_registry_param(T)  \
   `ovm_object_create_func(T) \
   `ovm_field_utils_begin(T) 

`define ovm_object_utils_end \
     end \
   endfunction \


// MACRO: `ovm_component_utils

// MACRO: `ovm_component_param_utils

// MACRO: `ovm_component_utils_begin

// MACRO: `ovm_component_param_utils_begin

// MACRO: `ovm_component_end
//
// ovm_component-based class declarations may contain one of the above forms of
// utility macros.
//
// For simple components with no field macros, use
//
//|  `ovm_component_utils(TYPE)
//
// For simple components with field macros, use
//
//|  `ovm_component_utils_begin(TYPE)
//|    `ovm_field_* macro invocations here
//|  `ovm_component_utils_end
//
// For parameterized components with no field macros, use
//
//|  `ovm_component_param_utils(TYPE)
//
// For parameterized components with field macros, use
//
//|  `ovm_component_param_utils_begin(TYPE)
//|    `ovm_field_* macro invocations here
//|  `ovm_component_utils_end
//
// Simple (non-parameterized) components must use the ovm_components_utils*
// versions, which do the following:
//
// o Implements get_type_name, which returns TYPE as a string.
//
// o Implements create, which allocates a component of type TYPE using a two
//   argument constructor. TYPE's constructor must have a name and a parent
//   argument.
//
// o Registers the TYPE with the factory, using the string TYPE as the factory
//   lookup string for the type.
//
// o Implements the static get_type() method which returns a factory
//   proxy object for the type.
//
// o Implements the virtual get_object_type() method which works just like the
//   static get_type() method, but operates on an already allocated object.
//
// Parameterized classes must use the ovm_object_param_utils* versions. They
// differ from `ovm_object_utils only in that they do not supply a type name
// when registering the object with the factory. As such, name-based lookup with
// the factory for parameterized classes is not possible.
//
// The macros with _begin suffixes are the same as the non-suffixed versions
// except that they also start a block in which `ovm_field_* macros can be
// placed. The block must be terminated by `ovm_component_utils_end.
//
// Components deriving from ovm_sequencer must use the `ovm_sequencer_* macros
// instead of these macros.  See `ovm_sequencer_utils for details.

`define ovm_component_utils(T) \
   `ovm_component_registry_internal(T,T) \
   `ovm_get_type_name_func(T) \

`define ovm_component_param_utils(T) \
   `ovm_component_registry_param(T) \

`define ovm_component_utils_begin(T) \
   `ovm_component_registry_internal(T,T) \
   `ovm_get_type_name_func(T) \
   `ovm_field_utils_begin(T) 

`define ovm_component_param_utils_begin(T) \
   `ovm_component_registry_param(T) \
   `ovm_field_utils_begin(T) 

`define ovm_component_utils_end \
     end \
   endfunction


//------------------------------------------------------------------------------
//
// Group: Field Macros
//
// The `ovm_field_*  macros are invoked inside of the `ovm_*_utils_begin and
// `ovm_*_utils_end macro blocks to form "automatic" implementations of the
// core data methods: copy, compare, pack, unpack, record, print, and sprint.
// For example:
//
//|  class my_trans extends ovm_transaction;
//|    string my_string;
//|    `ovm_object_utils_begin(my_trans)
//|      `ovm_field_string(my_string, OVM_ALL_ON)
//|    `ovm_object_utils_end
//|  endclass
//
// Each `ovm_field_* macro is named to correspond to a particular data
// type: integrals, strings, objects, queues, etc., and each has at least two
// arguments: ~ARG~ and ~FLAG~.
//
// ~ARG~ is the instance name of the variable, whose type must be compatible with
// the macro being invoked. In the example, class variable my_string is of type
// string, so we use the `ovm_field_string macro.
//
// If ~FLAG~ is set to ~OVM_ALL_ON~, as in the example, the ARG variable will be
// included in all data methods. The FLAG, if set to something other than
// ~OVM_ALL_ON~ or ~OVM_DEFAULT~, specifies which data method implementations will
// NOT include the given variable. Thus, if ~FLAG~ is specified as ~NO_COMPARE~,
// the ARG variable will not affect comparison operations, but it will be
// included in everything else.
//
// All possible values for ~FLAG~ are listed and described below. Multiple flag
// values can be bitwise ORed together (in most cases they may be added together
// as well, but care must be taken when using the + operator to ensure that the
// same bit is not added more than once).
//
//   OVM_ALL_ON     - Set all operations on (default).
//   OVM_DEFAULT    - Use the default flag settings.
//   OVM_NOCOPY     - Do not copy this field.
//   OVM_NOCOMPARE  - Do not compare this field.
//   OVM_NOPRINT    - Do not print this field.
//   OVM_NODEFPRINT - Do not print the field if it is the same as its
//   OVM_NOPACK     - Do not pack or unpack this field.
//   OVM_PHYSICAL   - Treat as a physical field. Use physical setting in
//                      policy class for this field.
//   OVM_ABSTRACT   - Treat as an abstract field. Use the abstract setting
//                      in the policy class for this field.
//   OVM_READONLY   - Do not allow setting of this field from the set_*_local
//                      methods.
//
// A radix for printing and recording can be specified by OR'ing one of the
// following constants in the ~FLAG~ argument
//
//   OVM_BIN      - Print / record the field in binary (base-2).
//   OVM_DEC      - Print / record the field in decimal (base-10).
//   OVM_UNSIGNED - Print / record the field in unsigned decimal (base-10).
//   OVM_OCT      - Print / record the field in octal (base-8).
//   OVM_HEX      - Print / record the field in hexidecimal (base-16).
//   OVM_STRING   - Print / record the field in string format.
//   OVM_TIME     - Print / record the field in time format.
//
//   Radix settings for integral types. Hex is the default radix if none is
//   specified.
//------------------------------------------------------------------------------

//-----------------------------------------------------------------------------
// Group: `ovm_field_* macros
//
// Macros that implement data operations for scalar properties.
//
//-----------------------------------------------------------------------------

// MACRO: `ovm_field_int
//
// Implements the data operations for any packed integral property.
//
//|  `ovm_field_int(ARG,FLAG)
//
// ~ARG~ is an integral property of the class, and ~FLAG~ is a bitwise OR of
// one or more flag settings as described in <Field Macros> above.

`define ovm_field_int(ARG,FLAG) \
  begin \
  if(what__==OVM_CHECK_FIELDS) m_do_field_check(`"ARG`"); \
  m_sc.scope.set_arg(`"ARG`"); \
  `M_OVM_FIELD_DATA(ARG,FLAG) \
  `M_OVM_FIELD_SET(ARG,FLAG) \
  m_sc.scope.unset_arg(`"ARG`"); \
  end


// MACRO: `ovm_field_object
//
// Implements the data operations for an <ovm_object>-based property.
//
//|  `ovm_field_object(ARG,FLAG)
//
// ~ARG~ is an object property of the class, and ~FLAG~ is a bitwise OR of
// one or more flag settings as described in <Field Macros> above.

`define ovm_field_object(ARG,FLAG) \
  if((ARG==null) || !m_sc.scope.in_hierarchy(ARG)) begin \
    if(what__==OVM_CHECK_FIELDS) m_do_field_check(`"ARG`"); \
    m_sc.scope.down(`"ARG`", ARG); \
    `M_OVM_FIELD_DATA_OBJECT(ARG,FLAG) \
    `M_OVM_FIELD_SET_OBJECT(ARG,FLAG) \
    m_sc.scope.up(ARG); \
  end


// MACRO: `ovm_field_string
//
// Implements the data operations for a string property.
//
//|  `ovm_field_string(ARG,FLAG)
//
// ~ARG~ is a string property of the class, and ~FLAG~ is a bitwise OR of
// one or more flag settings as described in <Field Macros> above.

`define ovm_field_string(ARG,FLAG) \
  begin \
  if(what__==OVM_CHECK_FIELDS) m_do_field_check(`"ARG`"); \
  m_sc.scope.down(`"ARG`",null); \
  `M_OVM_FIELD_DATA_STRING(ARG,FLAG) \
  `M_OVM_FIELD_SET_STRING(ARG,FLAG) \
  m_sc.scope.up(null); \
  end


// MACRO: `ovm_field_enum
// 
// Implements the data operations for an enumerated property.
//
//|  `ovm_field_enum(T,ARG,FLAG)
//
// ~T~ is an enumerated _type_, ~ARG~ is an instance of that type, and
// ~FLAG~ is a bitwise OR of one or more flag settings as described in
// <Field Macros> above.

`define ovm_field_enum(T,ARG,FLAG) \
  begin \
  m_sc.scope.set_arg(`"ARG`"); \
  `M_OVM_FIELD_ENUM(T,ARG,FLAG) \
  m_sc.scope.unset_arg(`"ARG`"); \
  end


// MACRO: `ovm_field_real
//
// Implements the data operations for any real property.
//
//|  `ovm_field_real(ARG,FLAG)
//
// ~ARG~ is an real property of the class, and ~FLAG~ is a bitwise OR of
// one or more flag settings as described in <Field Macros> above.

`define ovm_field_real(ARG,FLAG) \
  begin \
  if(what__==OVM_CHECK_FIELDS) m_do_field_check(`"ARG`"); \
  m_sc.scope.set_arg(`"ARG`"); \
  if((local_data__ != null) && $cast(local_data__, tmp_data__)) \
    void'(m_do_data_real(`"ARG`", ARG, local_data__.ARG, what__, FLAG)); \
  else \
    void'(m_do_data_real(`"ARG`", ARG, 0, what__, FLAG)); \
  m_sc.scope.unset_arg(`"ARG`"); \
  end


// MACRO: `ovm_field_event
//   
// Implements the data operations for an event property.
//
//|  `ovm_field_event(ARG,FLAG)
//
// ~ARG~ is an event property of the class, and ~FLAG~ is a bitwise OR of
// one or more flag settings as described in <Field Macros> above.

`define ovm_field_event(ARG,FLAG) \
  begin \
  if(what__==OVM_CHECK_FIELDS) m_do_field_check(`"ARG`"); \
  m_sc.scope.down(`"ARG`", null); \
  `M_OVM_FIELD_DATA_EVENT(ARG,FLAG) \
  m_sc.scope.up(null); \
  end
     


//-----------------------------------------------------------------------------
// Group: `ovm_field_sarray_* macros
//                            
// Macros that implement data operations for one-dimensional static array
// properties.
//-----------------------------------------------------------------------------

// MACRO: `ovm_field_sarray_int
//
// Implements the data operations for a one-dimensional static array of
// integrals.
//
//|  `ovm_field_sarray_int(ARG,FLAG)
//
// ~ARG~ is a one-dimensional static array of integrals, and ~FLAG~
// is a bitwise OR of one or more flag settings as described in
// <Field Macros> above.

`define ovm_field_sarray_int(ARG,FLAG) \
  begin \
  if(what__==OVM_CHECK_FIELDS) m_do_field_check(`"ARG`"); \
  m_sc.scope.down(`"ARG`",null); \
  `M_OVM_FIELD_DATA_SARRAY(ARG,FLAG) \
  `M_OVM_FIELD_SET_SARRAY_TYPE(INT,ARG,m_sc.bitstream,FLAG) \
  m_sc.scope.up(null); \
  end


// MACRO: `ovm_field_sarray_object
//
// Implements the data operations for a one-dimensional static array of
// <ovm_object>-based objects.
//
//|  `ovm_field_sarray_object(ARG,FLAG)
//
// ~ARG~ is a one-dimensional static array of <ovm_object>-based objects,
// and ~FLAG~ is a bitwise OR of one or more flag settings as described in
// <Field Macros> above.

`define ovm_field_sarray_object(ARG,FLAG) \
  begin \
  if(what__==OVM_CHECK_FIELDS) m_do_field_check(`"ARG`"); \
  m_sc.scope.down(`"ARG`",null); \
  `M_OVM_FIELD_DATA_SARRAY_OBJECT(ARG,FLAG) \
  `M_OVM_FIELD_SET_SARRAY_OBJECT(ARG,FLAG) \
  m_sc.scope.up(null); \
  end


// MACRO: `ovm_field_sarray_string
//
// Implements the data operations for a one-dimensional static array of
// strings.
//
//|  `ovm_field_sarray_string(ARG,FLAG)
//
// ~ARG~ is a one-dimensional static array of strings, and ~FLAG~ is a bitwise
// OR of one or more flag settings as described in <Field Macros> above.

`define ovm_field_sarray_string(ARG,FLAG) \
  begin \
  if(what__==OVM_CHECK_FIELDS) m_do_field_check(`"ARG`"); \
  m_sc.scope.down(`"ARG`", null); \
  `M_OVM_FIELD_DATA_SARRAY_STRING(ARG,FLAG) \
  `M_OVM_FIELD_SET_SARRAY_TYPE(STR, ARG, m_sc.stringv, FLAG) \
  m_sc.scope.up(null); \
  end 


// MACRO: `ovm_field_sarray_enum
//
// Implements the data operations for a one-dimensional static array of
// enums.
//
//|  `ovm_field_sarray_enum(T,ARG,FLAG)
//
// ~T~ is a one-dimensional dynamic array of enums _type_, ~ARG~ is an
// instance of that type, and ~FLAG~ is a bitwise OR of one or more flag
// settings as described in <Field Macros> above.

`define ovm_field_sarray_enum(T,ARG,FLAG) \
  begin \
    T lh__, rh__; \
    if(what__==OVM_CHECK_FIELDS) m_do_field_check(`"ARG`"); \
    m_sc.scope.down(`"ARG`",null); \
    if((what__ == OVM_PRINT) && !(OVM_NOPRINT&(FLAG))) \
      `ovm_print_qda_enum(ARG, ovm_auto_options_object.printer, array, T) \
    else if((what__ == OVM_COPY) && !(OVM_NOCOPY&(FLAG))) begin \
      $cast(local_data__, tmp_data__); \
      if(local_data__ != null) foreach(ARG[i]) ARG[i] = local_data__.ARG[i]; \
    end \
    else if((what__ == OVM_RECORD) && !(OVM_NORECORD&(FLAG))) \
      `m_ovm_record_qda_enum(T,ARG, ovm_auto_options_object.recorder) \
    else if((what__ == OVM_COMPARE) && !(OVM_NOCOMPARE&(FLAG))) begin \
      foreach(ARG[i__]) \
        if(ARG[i__] !== local_data__.ARG[i__]) begin \
          lh__ = ARG[i__]; \
          rh__ = local_data__.ARG[i__]; \
          ovm_auto_options_object.comparer.scope.down_element(i__, null);\
          $swrite(m_sc.stringv, "lhs = %0s : rhs = %0s", \
            lh__.name(), rh__.name()); \
          ovm_auto_options_object.comparer.print_msg(m_sc.stringv); \
          ovm_auto_options_object.comparer.scope.up_element(null);\
        end \
    end \
    `ovm_pack_unpack_sarray_enum(T,ARG,FLAG) \
    `M_OVM_FIELD_SET_SARRAY_ENUM(T, ARG, m_sc.bitstream, FLAG) \
    m_sc.scope.up(null); \
  end


//-----------------------------------------------------------------------------
// Group: `ovm_field_array_* macros
//
// Macros that implement data operations for one-dimensional dynamic array
// properties.
//
//-----------------------------------------------------------------------------

// MACRO: `ovm_field_array_int
//
// Implements the data operations for a one-dimensional dynamic array of
// integrals.
//
//|  `ovm_field_array_int(ARG,FLAG)
//
// ~ARG~ is a one-dimensional dynamic array of integrals,
// and ~FLAG~ is a bitwise OR of one or more flag settings as described in
// <Field Macros> above.

`define ovm_field_array_int(ARG,FLAG) \
  begin \
  if(what__==OVM_CHECK_FIELDS) m_do_field_check(`"ARG`"); \
  m_sc.scope.down(`"ARG`",null); \
  if(what__==OVM_COPY && !((FLAG)&OVM_NOCOPY)) begin \
    if(local_data__!=null) begin \
      ARG = new [local_data__.ARG.size()](local_data__.ARG); \
    end \
    else begin \
      ARG.delete(); \
    end \
  end \
  `M_OVM_FIELD_DATA_ARRAY(ARG,FLAG) \
  `M_OVM_FIELD_ARRAY_INT_PACK(ARG,FLAG) \
  `M_OVM_FIELD_SET_ARRAY_TYPE(INT, ARG, m_sc.bitstream, FLAG) \
  m_sc.scope.up(null); \
  end


// MACRO: `ovm_field_array_object
//
// Implements the data operations for a one-dimensional dynamic array
// of <ovm_object>-based objects.
//
//|  `ovm_field_array_object(ARG,FLAG)
//
// ~ARG~ is a one-dimensional dynamic array of <ovm_object>-based objects,
// and ~FLAG~ is a bitwise OR of one or more flag settings as described in
// <Field Macros> above.

`define ovm_field_array_object(ARG,FLAG) \
  begin \
    if(what__==OVM_CHECK_FIELDS) m_do_field_check(`"ARG`"); \
    m_sc.scope.down(`"ARG`", null); \
    if(what__==OVM_COPY && !((FLAG)&OVM_NOCOPY)) begin \
      if(local_data__!=null) begin \
         if(ARG.size() != local_data__.ARG.size()) \
           ARG = new[local_data__.ARG.size()](ARG); \
      end \
      else begin \
        ARG.delete(); \
      end \
    end \
    `M_OVM_FIELD_DATA_ARRAY_OBJECT(ARG,FLAG) \
    `M_OVM_FIELD_ARRAY_OBJ_PACK(ARG,FLAG) \
    `M_OVM_FIELD_SET_ARRAY_OBJECT(ARG,FLAG) \
    m_sc.scope.up(null); \
  end 


// MACRO: `ovm_field_array_string
//
// Implements the data operations for a one-dimensional dynamic array 
// of strings.
//
//|  `ovm_field_array_string(ARG,FLAG)
//
// ~ARG~ is a one-dimensional dynamic array of strings, and ~FLAG~ is a bitwise
// OR of one or more flag settings as described in <Field Macros> above.

`define ovm_field_array_string(ARG,FLAG) \
  begin \
  if(what__==OVM_CHECK_FIELDS) m_do_field_check(`"ARG`"); \
  m_sc.scope.down(`"ARG`", null); \
  if(what__==OVM_COPY && !((FLAG)&OVM_NOCOPY)) begin \
    if(local_data__!=null) begin \
       ARG = new[local_data__.ARG.size()]; \
    end \
    else begin \
      ARG.delete(); \
    end \
  end \
  `M_OVM_FIELD_DATA_ARRAY_STRING(ARG,FLAG) \
  `M_OVM_FIELD_ARRAY_STR_PACK(ARG,FLAG) \
  `M_OVM_FIELD_SET_ARRAY_TYPE(STR, ARG, m_sc.stringv, FLAG) \
  m_sc.scope.up(null); \
  end 


// MACRO: `ovm_field_array_enum
//
// Implements the data operations for a one-dimensional dynamic array of
// enums.
//
//|  `ovm_field_array_enum(T,ARG,FLAG)
//
// ~T~ is a one-dimensional dynamic array of enums _type_,
// ~ARG~ is an instance of that type, and ~FLAG~ is a bitwise OR of
// one or more flag settings as described in <Field Macros> above.

`define ovm_field_array_enum(T,ARG,FLAG) \
  begin \
    `ovm_field_qda_enum(T,ARG,FLAG) \
    `ovm_unpack_array_enum(T,ARG,FLAG) \
    `M_OVM_FIELD_SET_ARRAY_ENUM(T, ARG, m_sc.bitstream, FLAG) \
  end


//-----------------------------------------------------------------------------
// Group: `ovm_field_queue_* macros
//
// Macros that implement data operations for dynamic queues.
//
//-----------------------------------------------------------------------------

// MACRO: `ovm_field_queue_int
//
// Implements the data operations for a queue of integrals.
//
//|  `ovm_field_queue_int(ARG,FLAG)
//
// ~ARG~ is a one-dimensional queue of integrals,
// and ~FLAG~ is a bitwise OR of one or more flag settings as described in
// <Field Macros> above.

`define ovm_field_queue_int(ARG,FLAG) \
  begin \
  if(what__==OVM_CHECK_FIELDS) m_do_field_check(`"ARG`"); \
  m_sc.scope.down(`"ARG`", null); \
  if(what__==OVM_COPY && !((FLAG)&OVM_NOCOPY)) begin \
    if(local_data__!=null) begin \
      `M_RESIZE_QUEUE_NOCOPY(ovm_bitstream_t, ARG, local_data__.ARG.size()) \
    end \
    else begin \
      `M_RESIZE_QUEUE_NOCOPY(ovm_bitstream_t, ARG, 0) \
    end \
  end \
  `M_OVM_FIELD_DATA_ARRAY(ARG,FLAG) \
  `M_OVM_FIELD_QUEUE_INT_PACK(ARG,FLAG) \
  `M_OVM_FIELD_SET_QUEUE_TYPE(INT, ARG, m_sc.bitstream, FLAG) \
  m_sc.scope.up(null); \
  end


// MACRO: `ovm_field_queue_object
//
// Implements the data operations for a queue of <ovm_object>-based objects.
//
//|  `ovm_field_queue_object(ARG,FLAG)
//
// ~ARG~ is a one-dimensional queue of <ovm_object>-based objects,
// and ~FLAG~ is a bitwise OR of one or more flag settings as described in
// <Field Macros> above.

`define ovm_field_queue_object(ARG,FLAG) \
  begin \
    if(what__==OVM_CHECK_FIELDS) m_do_field_check(`"ARG`"); \
    m_sc.scope.down(`"ARG`", null); \
    if(what__==OVM_COPY && !((FLAG)&OVM_NOCOPY)) begin \
      if(local_data__!=null) begin \
        `M_RESIZE_QUEUE_OBJECT_NOCOPY(ARG, local_data__.ARG.size()) \
      end \
      else begin \
        `M_RESIZE_QUEUE_OBJECT_NOCOPY(ARG, 0) \
      end \
    end \
    `M_OVM_FIELD_DATA_ARRAY_OBJECT(ARG,FLAG) \
    `M_OVM_FIELD_QUEUE_OBJ_PACK(ARG,FLAG) \
    `M_OVM_FIELD_SET_QUEUE_OBJECT(ARG,FLAG) \
    m_sc.scope.up(null); \
  end


// MACRO: `ovm_field_queue_string
//
// Implements the data operations for a queue of strings.
//
//|  `ovm_field_queue_string(ARG,FLAG)
//
// ~ARG~ is a one-dimensional queue of strings, and ~FLAG~ is a bitwise
// OR of one or more flag settings as described in <Field Macros> above.

`define ovm_field_queue_string(ARG,FLAG) \
  begin \
  if(what__==OVM_CHECK_FIELDS) m_do_field_check(`"ARG`"); \
  m_sc.scope.down(`"ARG`", null); \
  if(what__==OVM_COPY && !((FLAG)&OVM_NOCOPY)) begin \
    if(local_data__!=null) begin \
      `M_RESIZE_QUEUE_NOCOPY(string, ARG, local_data__.ARG.size()) \
    end \
    else begin \
      `M_RESIZE_QUEUE_NOCOPY(string, ARG, 0) \
    end \
  end \
  `M_OVM_FIELD_DATA_ARRAY_STRING(ARG,FLAG) \
  `M_OVM_FIELD_QUEUE_STR_PACK(ARG,FLAG) \
  `M_OVM_FIELD_SET_QUEUE_TYPE(STR, ARG, m_sc.stringv, FLAG) \
  m_sc.scope.up(null); \
  end


// MACRO: `ovm_field_queue_enum
//
// Implements the data operations for a one-dimensional queue of enums.
//
//|  `ovm_field_queue_enum(T,ARG,FLAG)
//
// ~T~ is a queue of enums _type_, ~ARG~ is an instance of that type,
// and ~FLAG~ is a bitwise OR of one or more flag settings as described
// in <Field Macros> above.

`define ovm_field_queue_enum(T,ARG,FLAG) \
  begin \
    `ovm_field_qda_enum(T,ARG,FLAG) \
    `ovm_unpack_queue_enum(T,ARG,FLAG) \
    `M_OVM_FIELD_SET_QUEUE_ENUM(T, ARG, m_sc.bitstream, FLAG) \
  end


//-----------------------------------------------------------------------------
// Group: `ovm_field_aa_*_string macros
//
// Macros that implement data operations for associative arrays indexed
// by ~string~.
//
//-----------------------------------------------------------------------------

// MACRO: `ovm_field_aa_int_string
//
// Implements the data operations for an associative array of integrals indexed
// by ~string~.
//
//|  `ovm_field_aa_int_string(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of integrals
// with string key, and ~FLAG~ is a bitwise OR of one or more flag settings as
// described in <Field Macros> above.

`define ovm_field_aa_int_string(ARG, FLAG) \
  begin \
  if(what__==OVM_CHECK_FIELDS) m_do_field_check(`"ARG`"); \
  m_sc.scope.down(`"ARG`", null); \
  `M_OVM_FIELD_DATA_AA_int_string(ARG,FLAG) \
  `M_OVM_FIELD_SET_AA_TYPE(string, INT, ARG, m_sc.bitstream, FLAG)  \
  m_sc.scope.up(null); \
  end


// MACRO: `ovm_field_aa_object_string
//
// Implements the data operations for an associative array of <ovm_object>-based
// objects indexed by ~string~.
//
//|  `ovm_field_aa_object_string(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of objects
// with string key, and ~FLAG~ is a bitwise OR of one or more flag settings as
// described in <Field Macros> above.

`define ovm_field_aa_object_string(ARG, FLAG) \
  begin \
  if(what__==OVM_CHECK_FIELDS) m_do_field_check(`"ARG`"); \
  m_sc.scope.down(`"ARG`", null); \
  `M_OVM_FIELD_DATA_AA_object_string(ARG,FLAG) \
  `M_OVM_FIELD_SET_AA_OBJECT_TYPE(string, ARG, FLAG)  \
  m_sc.scope.up(null); \
  end


// MACRO: `ovm_field_aa_string_string
//
// Implements the data operations for an associative array of strings indexed
// by ~string~.
//
//|  `ovm_field_aa_string_string(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of strings
// with string key, and ~FLAG~ is a bitwise OR of one or more flag settings as
// described in <Field Macros> above.

`define ovm_field_aa_string_string(ARG, FLAG) \
  begin \
  if(what__==OVM_CHECK_FIELDS) m_do_field_check(`"ARG`"); \
  m_sc.scope.down(`"ARG`", null); \
  `M_OVM_FIELD_DATA_AA_string_string(ARG,FLAG) \
  `M_OVM_FIELD_SET_AA_TYPE(string, STR, ARG, m_sc.stringv, FLAG)  \
  m_sc.scope.up(null); \
  end


//-----------------------------------------------------------------------------
// Group: `ovm_field_aa_*_int macros
//
// Macros that implement data operations for associative arrays indexed by an
// integral type.
//
//-----------------------------------------------------------------------------

// MACRO: `ovm_field_aa_object_int
//
// Implements the data operations for an associative array of <ovm_object>-based
// objects indexed by the ~int~ data type.
//
//|  `ovm_field_aa_object_int(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of objects
// with ~int~ key, and ~FLAG~ is a bitwise OR of one or more flag settings as
// described in <Field Macros> above.

`define ovm_field_aa_object_int(ARG, FLAG) \
  begin \
  if(what__==OVM_CHECK_FIELDS) m_do_field_check(`"ARG`"); \
  m_sc.scope.down(`"ARG`", null); \
  `M_OVM_FIELD_DATA_AA_object_int(ARG,FLAG) \
  `M_OVM_FIELD_SET_AA_OBJECT_TYPE(int, ARG, FLAG)  \
  m_sc.scope.up(null); \
  end


// MACRO: `ovm_field_aa_int_int
//
// Implements the data operations for an associative array of integral
// types indexed by the ~int~ data type.
//
//|  `ovm_field_aa_int_int(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of integrals
// with ~int~ key, and ~FLAG~ is a bitwise OR of one or more flag settings as
// described in <Field Macros> above.

`define ovm_field_aa_int_int(ARG, FLAG) \
  `ovm_field_aa_int_key(int, ARG, FLAG) \


// MACRO: `ovm_field_aa_int_int_unsigned
//
// Implements the data operations for an associative array of integral
// types indexed by the ~int unsigned~ data type.
//
//|  `ovm_field_aa_int_int_unsigned(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of integrals
// with ~int unsigned~ key, and ~FLAG~ is a bitwise OR of one or more flag
// settings as described in <Field Macros> above.

`define ovm_field_aa_int_int_unsigned(ARG, FLAG) \
  `ovm_field_aa_int_key(int unsigned, ARG, FLAG)


// MACRO: `ovm_field_aa_int_integer
//
// Implements the data operations for an associative array of integral
// types indexed by the ~integer~ data type.
//
//|  `ovm_field_aa_int_integer(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of integrals
// with ~integer~ key, and ~FLAG~ is a bitwise OR of one or more flag settings
// as described in <Field Macros> above.

`define ovm_field_aa_int_integer(ARG, FLAG) \
  `ovm_field_aa_int_key(integer, ARG, FLAG)


// MACRO: `ovm_field_aa_int_integer_unsigned
//
// Implements the data operations for an associative array of integral
// types indexed by the ~integer unsigned~ data type.
//
//|  `ovm_field_aa_int_integer_unsigned(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of integrals
// with ~integer unsigned~ key, and ~FLAG~ is a bitwise OR of one or more 
// flag settings as described in <Field Macros> above.

`define ovm_field_aa_int_integer_unsigned(ARG, FLAG) \
  `ovm_field_aa_int_key(integer unsigned, ARG, FLAG)


// MACRO: `ovm_field_aa_int_byte
//
// Implements the data operations for an associative array of integral
// types indexed by the ~byte~ data type.
//
//|  `ovm_field_aa_int_byte(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of integrals
// with ~byte~ key, and ~FLAG~ is a bitwise OR of one or more flag settings as
// described in <Field Macros> above.

`define ovm_field_aa_int_byte(ARG, FLAG) \
  `ovm_field_aa_int_key(byte, ARG, FLAG)


// MACRO: `ovm_field_aa_int_byte_unsigned
//
// Implements the data operations for an associative array of integral
// types indexed by the ~byte unsigned~ data type.
//
//|  `ovm_field_aa_int_byte_unsigned(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of integrals
// with ~byte unsigned~ key, and ~FLAG~ is a bitwise OR of one or more flag
// settings as described in <Field Macros> above.

`define ovm_field_aa_int_byte_unsigned(ARG, FLAG) \
  `ovm_field_aa_int_key(byte unsigned, ARG, FLAG)


// MACRO: `ovm_field_aa_int_shortint
//
// Implements the data operations for an associative array of integral
// types indexed by the ~shortint~ data type.
//
//|  `ovm_field_aa_int_shortint(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of integrals
// with ~shortint~ key, and ~FLAG~ is a bitwise OR of one or more flag
// settings as described in <Field Macros> above.

`define ovm_field_aa_int_shortint(ARG, FLAG) \
  `ovm_field_aa_int_key(shortint, ARG, FLAG)


// MACRO: `ovm_field_aa_int_shortint_unsigned
//
// Implements the data operations for an associative array of integral
// types indexed by the ~shortint unsigned~ data type.
//
//|  `ovm_field_aa_int_shortint_unsigned(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of integrals
// with ~shortint unsigned~ key, and ~FLAG~ is a bitwise OR of one or more
// flag settings as described in <Field Macros> above.

`define ovm_field_aa_int_shortint_unsigned(ARG, FLAG) \
  `ovm_field_aa_int_key(shortint unsigned, ARG, FLAG)


// MACRO: `ovm_field_aa_int_longint
//
// Implements the data operations for an associative array of integral
// types indexed by the ~longint~ data type.
//
//|  `ovm_field_aa_int_longint(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of integrals
// with ~longint~ key, and ~FLAG~ is a bitwise OR of one or more flag settings
// as described in <Field Macros> above.

`define ovm_field_aa_int_longint(ARG, FLAG) \
  `ovm_field_aa_int_key(longint, ARG, FLAG)


// MACRO: `ovm_field_aa_int_longint_unsigned
//
// Implements the data operations for an associative array of integral
// types indexed by the ~longint unsigned~ data type.
//
//|  `ovm_field_aa_int_longint_unsigned(ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of integrals
// with ~longint unsigned~ key, and ~FLAG~ is a bitwise OR of one or more
// flag settings as described in <Field Macros> above.

`define ovm_field_aa_int_longint_unsigned(ARG, FLAG) \
  `ovm_field_aa_int_key(longint unsigned, ARG, FLAG)


// MACRO: `ovm_field_aa_int_key
//
// Implements the data operations for an associative array of integral
// types indexed by any integral key data type. 
//
//|  `ovm_field_aa_int_key(KEY,ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of integrals
// indexed by the integral type, ~KEY~. ~FLAG~ is a bitwise OR of one or more
// flag settings as described in <Field Macros> above.

`define ovm_field_aa_int_key(KEY, ARG, FLAG) \
  begin \
  if(what__==OVM_CHECK_FIELDS) m_do_field_check(`"ARG`"); \
  m_sc.scope.down(`"ARG`", null); \
  `M_OVM_FIELD_DATA_AA_int_key(KEY,ARG,FLAG) \
  `M_OVM_FIELD_SET_AA_INT_TYPE(KEY, INT, ARG, m_sc.bitstream, FLAG)  \
  m_sc.scope.up(null); \
  end


// MACRO: `ovm_field_aa_int_enumkey
//
// Implements the data operations for an associative array of integral
// types indexed by any enumeration key data type. 
//
//|  `ovm_field_aa_int_enumkey(KEY,ARG,FLAG)
//
// ~ARG~ is the name of a property that is an associative array of
// integrals indexed by the enumeration data type, ~KEY~. ~FLAG~ is a bitwise
// OR of one or more flag settings as described in <Field Macros> above.

`define ovm_field_aa_int_enumkey(KEY, ARG, FLAG) \
  begin \
  if(what__==OVM_CHECK_FIELDS) m_do_field_check(`"ARG`"); \
  m_sc.scope.down(`"ARG`", null); \
  `M_OVM_FIELD_DATA_AA_enum_key(KEY,ARG,FLAG) \
  `M_OVM_FIELD_SET_AA_INT_ENUMTYPE(KEY, INT, ARG, m_sc.bitstream, FLAG)  \
  m_sc.scope.up(null); \
  end

//-----------------------------------------------------------------------------
//
// MACROS- recording
//
//-----------------------------------------------------------------------------

// m_ovm_record_int
// --------------

// Purpose: provide print functionality for a specific integral field. This
// macro is available for user access. If used externally, a record_options
// object must be avaialble and must have the name opt.
// 
// Postcondition: ~ARG~ is printed using the format set by the FLAGS.

`define m_ovm_record_int(ARG,FLAG) \
  begin \
    int radix__; \
    ovm_bitstream_t value; \
    value = ARG; \
    radix__ = ovm_radix_enum'((FLAG)&(OVM_RADIX)); \
    if(recorder==null) \
      recorder=ovm_auto_options_object.recorder; \
    recorder.record_field(`"ARG`", ARG, radix__, $bits(ARG); \
  end 


// m_ovm_record_string
// -----------------

// Purpose: provide record functionality for a specific string field. This
// macro is available for user access. If used externally, a record_options
// object must be avaialble and must have the name recorder.
//  
// Postcondition: ~ARG~ is recorded in string format.
      

`define m_ovm_record_string(ARG) \
  recorder.record_string(`"ARG`", ARG); \


// m_ovm_record_object
// -----------------

// Purpose: provide record functionality for a specific <ovm_object> field. This
// macro is available for user access. If used externally, a record_options
// object must be avaialble and must have the name recorder.
//
// Postcondition: ~ARG~ is recorded. The record is done recursively where the
// depth to record is set in the recorder object.


`define m_ovm_record_object(ARG,FLAG) \
  begin \
     ovm_object v__; \
     if(ARG != null) begin \
       if($cast(v__,ARG)) begin \
         ovm_record_object__(`"ARG`", v__, recorder); \
       end \
     end \
     else begin \
       `m_ovm_record_any_object(ARG); \
     end \
  end


// m_ovm_record_any_object
// ---------------------

// Purpose: provide record functionality for a user specific class object. This
// macro is available for user access. If used externally, a record_options
// object must be availble and must have the name recorder.
//
// Postcondition: The reference value of ~ARG~ is recorded.

`define m_ovm_record_any_object(ARG) \
  //recorder.record_object(`"ARG`", ARG);  


//-----------------------------------------------------------------------------
//
// INTERNAL MACROS - do not use directly
//
//-----------------------------------------------------------------------------


// Purpose: Provide a way for a derived class to override the flag settings in
// the base class.
//

`define ovm_set_flags(ARG,FLAG) \
  begin \
   if(what__ == OVM_FLAGS) begin \
   end \
  end


`define ovm_unpack_array_enum(T,ARG,FLAG) \
  if((what__ == OVM_UNPACK) && !(OVM_NOPACK&(FLAG))) begin \
    if((((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) || \
        (!((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) begin \
      if(ovm_auto_options_object.packer.use_metadata) begin \
        int s_; \
        s_ = ovm_auto_options_object.packer.unpack_field_int(32); \
        ARG = new[s_]; \
      end \
      foreach(ARG[i]) \
        ARG[i] = T'(ovm_auto_options_object.packer.unpack_field($bits(ARG[i]))); \
    end \
  end


`define ovm_unpack_queue_enum(T,ARG,FLAG) \
  if((what__ == OVM_UNPACK) && !(OVM_NOPACK&(FLAG))) begin \
    if((((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) || \
        (!((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) begin \
      if(ovm_auto_options_object.packer.use_metadata) begin \
        int s_; \
        s_ = ovm_auto_options_object.packer.unpack_field_int(32); \
        while(ARG.size() > s_) void'(ARG.pop_front()); \
        while(ARG.size() < s_) ARG.push_back(T'(0)); \
      end \
      foreach(ARG[i]) \
        ARG[i] = T'(ovm_auto_options_object.packer.unpack_field($bits(ARG[i]))); \
    end \
  end \


`define ovm_pack_unpack_sarray_enum(T,ARG,FLAG) \
  if((what__ == OVM_PACK) && !(OVM_NOPACK&(FLAG))) begin \
    if((((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) || \
        (!((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) \
      foreach(ARG[i]) \
        ovm_auto_options_object.packer.pack_field(ARG[i],$bits(ARG[i])); \
  end \
  else if((what__ == OVM_UNPACK) && !(OVM_NOPACK&(FLAG))) begin \
    if((((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) || \
        (!((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) \
      foreach(ARG[i]) \
        ARG[i] = T'(ovm_auto_options_object.packer.unpack_field($bits(ARG[i]))); \
  end \


`define ovm_field_qda_enum(T,ARG,FLAG) \
  begin \
    T lh__, rh__; \
    if(what__==OVM_CHECK_FIELDS) m_do_field_check(`"ARG`"); \
    m_sc.scope.down(`"ARG`",null); \
    if((what__ == OVM_PRINT) && !(OVM_NOPRINT&(FLAG))) \
      `ovm_print_qda_enum(ARG, ovm_auto_options_object.printer, array, T) \
    else if((what__ == OVM_RECORD) && !(OVM_NORECORD&(FLAG))) \
      `m_ovm_record_qda_enum(T,ARG, ovm_auto_options_object.recorder) \
    else if((what__ == OVM_COMPARE) && !(OVM_NOCOMPARE&(FLAG))) begin \
      $cast(local_data__, tmp_data__); \
      if(ARG.size() != local_data__.ARG.size()) begin \
        int s1__, s2__; \
        m_sc.stringv = ""; \
        s1__ = ARG.size(); s2__ = local_data__.ARG.size(); \
        $swrite(m_sc.stringv, "lhs size = %0d : rhs size = %0d", s1__, s2__);\
        ovm_auto_options_object.comparer.print_msg(m_sc.stringv); \
      end \
      for(int i__=0; i__<ARG.size() && i__<local_data__.ARG.size(); ++i__) \
        if(ARG[i__] !== local_data__.ARG[i__]) begin \
          lh__ = ARG[i__]; \
          rh__ = local_data__.ARG[i__]; \
          ovm_auto_options_object.comparer.scope.down_element(i__, null);\
          $swrite(m_sc.stringv, "lhs = %0s : rhs = %0s", \
            lh__.name(), rh__.name()); \
          ovm_auto_options_object.comparer.print_msg(m_sc.stringv); \
          ovm_auto_options_object.comparer.scope.up_element(null);\
        end \
    end \
    if((what__ == OVM_COPY) && !(OVM_NOCOPY&(FLAG))) begin \
      $cast(local_data__, tmp_data__); \
      if(local_data__ != null) ARG = local_data__.ARG; \
    end \
    else if((what__ == OVM_PACK) && !(OVM_NOPACK&(FLAG))) begin \
      if(ovm_auto_options_object.packer.use_metadata == 1) \
        ovm_auto_options_object.packer.pack_field_int(ARG.size(), 32); \
      foreach(ARG[i]) \
        ovm_auto_options_object.packer.pack_field(int'(ARG[i]), $bits(ARG[i])); \
    end \
    m_sc.scope.up(null); \
  end


// ovm_new_func
// ------------

`define ovm_new_func \
  function new (string name, ovm_component parent); \
    super.new(name, parent); \
  endfunction

`define ovm_component_new_func \
  `ovm_new_func

`define ovm_new_func_data \
  function new (string name=""); \
    super.new(name); \
  endfunction

`define ovm_object_new_func \
  `ovm_new_func_data

`define ovm_named_object_new_func \
  function new (string name, ovm_component parent); \
    super.new(name, parent); \
  endfunction


// ovm_object_create_func
// ----------------------

// Zero argument create function, requires default constructor
`define ovm_object_create_func(T) \
   function ovm_object create (string name=""); \
     T tmp; \
     tmp = new(); \
     if (name!="") \
       tmp.set_name(name); \
     return tmp; \
   endfunction


// ovm_named_object_create_func
// ----------------------------

`define ovm_named_object_create_func(T) \
   function ovm_named_object create_named_object (string name, ovm_named_object parent); \
     T tmp; \
     tmp = new(.name(name), .parent(parent)); \
     return tmp; \
   endfunction


`define ovm_named_object_factory_create_func(T) \
  `ovm_named_object_create_func(T) \


// ovm_object_factory_create_func
// ------------------------------

`define ovm_object_factory_create_func(T) \
   function ovm_object create_object (string name=""); \
     T tmp; \
     tmp = new(); \
     if (name!="") \
       tmp.set_name(name); \
     return tmp; \
   endfunction \
   \
   static function T create(string name="", ovm_component parent=null, string contxt=""); \
     ovm_factory f; \
     f = ovm_factory::get(); \
     if (contxt == "" && parent != null) \
       contxt = parent.get_full_name(); \
     if(!$cast(create,f.create_object_by_type(get(),contxt,name))) \
        ovm_top.ovm_report_fatal("FACTFL", {"Factory did not return an object of type, ",type_name}, OVM_NONE); \
   endfunction


// ovm_component_factory_create_func
// ---------------------------------

`define ovm_component_factory_create_func(T) \
   function ovm_component create_component (string name, ovm_component parent); \
     T tmp; \
     tmp = new(.name(name), .parent(parent)); \
     return tmp; \
   endfunction \
   \
   static function T create(string name, ovm_component parent, string contxt=""); \
     ovm_factory f; \
     f = ovm_factory::get(); \
     if (contxt == "" && parent != null) \
       contxt = parent.get_full_name(); \
     if(!$cast(create,f.create_component_by_type(get(),contxt,name,parent))) \
        ovm_top.ovm_report_fatal("FACTFL", {"Factory did not return a component of type, ",type_name}, OVM_NONE); \
   endfunction


// ovm_get_type_name_func
// ----------------------

`define ovm_get_type_name_func(T) \
   const static string type_name = `"T`"; \
   virtual function string get_type_name (); \
     return type_name; \
   endfunction 


// ovm_register_self_func
// ----------------------

`ifndef INCA
`define USE_PARAMETERIZED_WRAPPER
`endif

`ifndef USE_PARAMETERIZED_WRAPPER
`define ovm_register_self_func(T) \
  \
  local static type_id me = get(); \
  \
  static function type_id get(); \
    ovm_factory f; \
    f = ovm_factory::get(); \
    if (me == null) begin \
      me = new(); \
      factory.register(me); \
    end \
    return me; \
  endfunction
`else
`define ovm_register_self_func(T)
`endif


`ifndef USE_PARAMETERIZED_WRAPPER
`define ovm_factory_override_func \
  static function void set_type_override(ovm_object_wrapper override, bit replace=1); \
    factory.set_type_override_by_type(get(),override,replace); \
  endfunction \
\
  static function void set_inst_override(ovm_object_wrapper override, \
                                         string inst_path, \
                                         ovm_component parent=null); \
    string full_inst_path; \
    if (parent != null) begin \
      if (inst_path == "") \
        inst_path = parent.get_full_name(); \
      else \
        inst_path = {parent.get_full_name(),".",inst_path}; \
    end \
    factory.set_inst_override_by_type(get(),override,inst_path); \
  endfunction
`else
`define ovm_factory_override_func
`endif
 

// ovm_object_derived_wrapper_class
// --------------------------------

//Requires S to be a constant string
`ifndef USE_PARAMETERIZED_WRAPPER
`define ovm_object_registry(T,S) \
   class type_id extends ovm_object_wrapper; \
     const static string type_name = S; \
     virtual function string get_type_name (); \
       return type_name; \
     endfunction \
     `ovm_object_factory_create_func(T) \
     `ovm_factory_override_func \
     `ovm_register_self_func(T) \
   endclass  \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function ovm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction 
//This is needed due to an issue in IUS of passing down strings
//created by args to lower level macros.
`define ovm_object_registry_internal(T,S) \
   class type_id extends ovm_object_wrapper; \
     const static string type_name = `"S`"; \
     virtual function string get_type_name (); \
       return type_name; \
     endfunction \
     `ovm_object_factory_create_func(T) \
     `ovm_factory_override_func \
     `ovm_register_self_func(T) \
   endclass  \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function ovm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction 
`else
`ifndef SVPP
`define ovm_object_registry(T,S) \
   typedef ovm_object_registry#(T,S) type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function ovm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction 
//This is needed due to an issue in IUS of passing down strings
//created by args to lower level macros.
`define ovm_object_registry_internal(T,S) \
   typedef ovm_object_registry#(T,`"S`") type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function ovm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction 
`endif //SVPP
`endif //USE_PARAMETERIZED_WRAPPER


// versions of the ovm_object_registry macros above which are to be used
// with parameterized classes

`ifndef USE_PARAMETERIZED_WRAPPER
`define ovm_object_registry_param(T) \
   class type_id extends ovm_object_wrapper; \
     const static string type_name = "<unknown>"; \
     virtual function string get_type_name (); \
       return type_name; \
     endfunction \
     `ovm_object_factory_create_func(T) \
     `ovm_factory_override_func \
     `ovm_register_self_func(T) \
   endclass  \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function ovm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction 
`else
`ifndef SVPP
`define ovm_object_registry_param(T) \
   typedef ovm_object_registry #(T) type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function ovm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction 
`endif //SVPP
`endif //USE_PARAMETERIZED_WRAPPER


// ovm_component_derived_wrapper_class
// ---------------------------------

`ifndef USE_PARAMETERIZED_WRAPPER
`define ovm_component_registry(T,S) \
   class type_id extends ovm_object_wrapper; \
     const static string type_name = S; \
     virtual function string get_type_name (); \
       return type_name; \
     endfunction \
     `ovm_component_factory_create_func(T) \
     `ovm_factory_override_func \
     `ovm_register_self_func(T) \
   endclass  \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function ovm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction 
//This is needed due to an issue in IUS of passing down strings
//created by args to lower level macros.
`define ovm_component_registry_internal(T,S) \
   class type_id extends ovm_object_wrapper; \
     const static string type_name = `"S`"; \
     virtual function string get_type_name (); \
       return type_name; \
     endfunction \
     `ovm_component_factory_create_func(T) \
     `ovm_factory_override_func \
     `ovm_register_self_func(T) \
   endclass  \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function ovm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction 
`else
`ifndef SVPP
`define ovm_component_registry(T,S) \
   typedef ovm_component_registry #(T,S) type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function ovm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction 
//This is needed due to an issue in IUS of passing down strings
//created by args to lower level macros.
`define ovm_component_registry_internal(T,S) \
   typedef ovm_component_registry #(T,`"S`") type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function ovm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction
`endif //SVPP
`endif //USE_PARAMETERIZED_WRAPPER

// versions of the ovm_component_registry macros to be used with
// parameterized classes

`ifndef USE_PARAMETERIZED_WRAPPER
`define ovm_component_registry_param(T) \
   class type_id extends ovm_object_wrapper; \
     const static string type_name = "<unknown>"; \
     virtual function string get_type_name (); \
       return type_name; \
     endfunction \
     `ovm_component_factory_create_func(T) \
     `ovm_factory_override_func \
     `ovm_register_self_func(T) \
   endclass  \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function ovm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction
`else
`ifndef SVPP
`define ovm_component_registry_param(T) \
   typedef ovm_component_registry #(T) type_id; \
   static function type_id get_type(); \
     return type_id::get(); \
   endfunction \
   virtual function ovm_object_wrapper get_object_type(); \
     return type_id::get(); \
   endfunction
`endif //SVPP
`endif //USE_PARAMETERIZED_WRAPPER


// ovm_print_msg_enum
// ------------------

`define ovm_print_msg_enum(LHS,RHS) \
  begin \
    ovm_comparer comparer; \
    comparer = ovm_auto_options_object.comparer; \
    if(comparer==null) comparer = ovm_default_comparer; \
    comparer.result++; \
/*    $swrite(comparer.miscompares,"%s%s: lhs = %s : rhs = %s\n",*/ \
/*       comparer.miscompares, comparer.scope.get_arg(), LHS, RHS );*/ \
    $swrite(comparer.miscompares,"%s%s: lhs = %0d : rhs = %0d\n", \
       comparer.miscompares, comparer.scope.get_arg(), LHS, RHS ); \
  end


// M_OVM_FIELD_DATA
// --------------

`define M_OVM_FIELD_DATA(ARG,FLAG) \
  begin \
    int r__; \
    if((what__ == OVM_PRINT) && (((FLAG)&OVM_NOPRINT) == 0) && (ovm_radix_enum'((FLAG)&OVM_RADIX) == OVM_ENUM) && \
        (ovm_auto_options_object.printer.knobs.print_fields == 1)) begin \
      $swrite(m_sc.stringv, "%0d", ARG); \
      ovm_auto_options_object.printer.print_generic(`"ARG`", "enum", \
          $bits(ARG), m_sc.stringv); \
    end \
    else if((what__ == OVM_RECORD) && (((FLAG)&OVM_NORECORD) == 0) && (ovm_radix_enum'((FLAG)&OVM_RADIX) == OVM_ENUM)) \
    begin \
      $swrite(m_sc.stringv, "%0d", ARG); \
      ovm_auto_options_object.recorder.record_string(`"ARG`",m_sc.stringv); \
    end \
    else if(tmp_data__!=null) begin \
      if($cast(local_data__, tmp_data__)) begin \
        r__ = m_do_data(`"ARG`", ARG, local_data__.ARG, what__, $bits(ARG), FLAG); \
      end \
    end \
    else begin \
      if(what__ != OVM_COMPARE && what__ != OVM_COPY) begin \
        r__ = m_do_data(`"ARG`", ARG, 0, what__, $bits(ARG), FLAG); \
      end \
    end \
    if((what__ == OVM_COMPARE) && r__) begin \
      if(ovm_radix_enum'((FLAG)&OVM_RADIX) == OVM_ENUM) begin \
        if(local_data__!=null) begin \
          `ovm_print_msg_enum(ARG, local_data__.ARG) \
        end \
        else begin \
          `ovm_print_msg_enum(ARG, 0) \
        end \
      end \
    end \
  end 

`define M_OVM_FIELD_ENUM(T, ARG,FLAG) \
  begin \
    T lh__=ARG, rh__; \
    if((what__ == OVM_PRINT) && (((FLAG)&OVM_NOPRINT) == 0) && \
        (ovm_auto_options_object.printer.knobs.print_fields == 1)) begin \
      ovm_auto_options_object.printer.print_generic(`"ARG`", `"T`", \
          $bits(ARG), lh__.name()); \
    end \
    else if((what__ == OVM_RECORD) && (((FLAG)&OVM_NORECORD) == 0)) \
    begin \
      ovm_auto_options_object.recorder.record_string(`"ARG`",lh__.name()); \
    end \
    else if(tmp_data__!=null) begin \
      if($cast(local_data__, tmp_data__)) begin \
        case(what__) \
          OVM_COPY: \
            if(((FLAG)&OVM_NOCOPY) == 0) \
               ARG = local_data__.ARG; \
          OVM_COMPARE: \
            if((((FLAG)&OVM_NOCOMPARE) == 0) && (ARG != local_data__.ARG)) begin \
               rh__ = local_data__.ARG; \
               ovm_auto_options_object.comparer.print_msg({"lhs = ", lh__.name(), " : rhs = ", rh__.name()}); \
            end \
        endcase \
      end \
    end \
    else begin \
      case(what__) \
        OVM_PACK: \
          if(((FLAG)&OVM_NOPACK) == 0) \
            if((((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) || \
                (!((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) begin \
              ovm_auto_options_object.packer.pack_field_int(int'(ARG), $bits(ARG)); \
            end \
        OVM_UNPACK: \
          begin \
          if((((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) || \
              (!((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) \
            if(((FLAG)&OVM_NOPACK) == 0) begin \
              ARG = T'(ovm_auto_options_object.packer.unpack_field_int($bits(ARG))); \
            end \
          end \
        OVM_SETINT: \
          begin \
            if(ovm_is_match(str__ ,m_sc.scope.get_arg()) && (((FLAG)&OVM_READONLY) == 0)) begin \
               print_field_match("set_int()", str__); \
               ARG = T'(ovm_object::m_sc.bitstream); \
               ovm_object::m_sc.status = 1; \
            end \
          end \
      endcase \
    end \
  end 

// M_OVM_FIELD_DATA_EVENT
// --------------------

`define M_OVM_FIELD_DATA_EVENT(ARG,FLAG) \
  begin \
    if(what__ == OVM_PRINT && ( (FLAG)&OVM_NOPRINT != 0) && \
                          ovm_auto_options_object.printer.knobs.print_fields == 1) \
       ovm_auto_options_object.printer.print_generic(`"ARG`", "event", -1, "-"); \
    else if((what__ == OVM_COMPARE) && ( (FLAG)&OVM_NOCOMPARE != 0) && \
            local_data__ && ARG != local_data__.ARG) \
    begin \
      ovm_auto_options_object.comparer.print_msg(""); \
    end \
    else if((what__ == OVM_COPY) && local_data__ && ( (FLAG)&OVM_NOCOPY != 0 ) ) \
    begin \
      ARG = local_data__.ARG; \
    end \
  end


// M_OVM_FIELD_DATA_OBJECT
// ---------------------

`define M_OVM_FIELD_DATA_OBJECT(ARG,FLAG) \
  begin \
    int r__; \
    ovm_object lhs__, rhs__; \
    r__ = 0; \
    if(ARG == null) \
      lhs__ = null; \
    else if(!$cast(lhs__,ARG)) begin \
      ovm_object::m_sc.scratch1 = \
        `"Cast failed for ARG to ovm_object type (ovm_field_object not implemented)`";  \
      _global_reporter.ovm_report_warning("CSTFLD",ovm_object::m_sc.scratch1, OVM_NONE); \
    end \
    if(tmp_data__ != null) begin \
      if($cast(local_data__, tmp_data__)) begin \
        r__ = m_do_data_object(`"ARG`", lhs__, local_data__.ARG, what__, FLAG); \
      end \
      else if(tmp_data__!=null) begin \
        ovm_object::m_sc.scratch1 = `"Type check failed for ARG for copy/compare`"; \
        _global_reporter.ovm_report_error("TCKFLD", ovm_object::m_sc.scratch1, OVM_NONE); \
      end \
    end \
    else begin \
      r__ = m_do_data_object(`"ARG`", lhs__, null, what__, FLAG); \
      if (what__ == OVM_UNPACK) begin \
        m_sc.scope.up(ARG); \
        if (lhs__ == null) ARG = null; \
        else if (!$cast(ARG,lhs__)) ARG = null; \
        m_sc.scope.down(`"ARG`",ARG); \
      end \
    end \
    /* if return is 1 then upack of the object failed, don't want to continue. */ \
    if(r__ == 1 && what__ == OVM_UNPACK) \
       return; \
    if((what__ == OVM_COPY) && (ovm_recursion_policy_enum'(r__) == OVM_SHALLOW)) begin \
      ovm_object v__; \
      m_sc.scope.up(ARG); \
      v__ = ovm_global_copy_map.get(local_data__.ARG); \
      if(v__ != null) begin \
        $cast(ARG, v__); \
      end \
      else begin \
        /* Can't do shallow copy right now due to */ \
        /* an issue with abstract classes */ \
        /* like ovm_object, so do a deep copy instead. */ \
        if(local_data__.ARG==null) ARG = null; \
        else if(ARG!=null) ARG.copy(local_data__.ARG); \
        else begin \
          ovm_object cobj; \
          cobj = local_data__.ARG.clone(); \
          if(cobj == null) ARG = null; \
          else begin \
            $cast(ARG, local_data__.ARG.clone()); \
            ARG.set_name(`"ARG`"); \
          end \
        end \
      end \
      m_sc.scope.down(`"ARG`",ARG); \
    end \
    else if((what__ == OVM_COPY) && (ovm_recursion_policy_enum'(r__) == OVM_REFERENCE)) begin \
      m_sc.scope.up(ARG); \
      if((lhs__ == null)&&(local_data__.ARG != null)) begin \
        if(!$cast(ARG,local_data__.ARG)) begin \
          ovm_object::m_sc.scratch1 = `"Copy cast failed for ARG`"; \
          _global_reporter.ovm_report_error("CSTFLD",ovm_object::m_sc.scratch1, OVM_NONE); \
        end \
      end \
      else if(lhs__==null) \
        ARG = null; \
      else \
        $cast(ARG, lhs__); \
      m_sc.scope.down(`"ARG`",ARG); \
    end \
  end


// M_OVM_FIELD_DATA_STRING
// ---------------------

`define M_OVM_FIELD_DATA_STRING(ARG,FLAG) \
  begin \
    int r__; \
    if(local_data__ != null) begin \
      if($cast(local_data__, tmp_data__)) begin \
        r__ = m_do_data_string(`"ARG`", ARG, local_data__.ARG, what__, FLAG); \
      end \
    end \
    else \
      r__ = m_do_data_string(`"ARG`", ARG, "", what__, FLAG); \
  end 


// M_RESIZE_QUEUE_NOCOPY
// -------------------

`define M_RESIZE_QUEUE_NOCOPY(T, ARG, SIZE) \
   begin \
     T tmp__; \
     while(ARG.size()) void'(ARG.pop_front()); \
     while(ARG.size() != SIZE) ARG.push_back(tmp__); \
   end 


// M_RESIZE_QUEUE_COPY
// -----------------

`define M_RESIZE_QUEUE_COPY(T, ARG, SIZE) \
   begin \
     T tmp__; \
     while(ARG.size()>SIZE) void'(ARG.pop_back()); \
     while(ARG.size() != SIZE) ARG.push_back(tmp__); \
   end


// M_RESIZE_QUEUE_OBJECT_NOCOPY
// --------------------------

`define M_RESIZE_QUEUE_OBJECT_NOCOPY(ARG, SIZE) \
   begin \
     while(ARG.size()>SIZE) void'(ARG.pop_front()); \
     while(ARG.size() != SIZE) ARG.push_back(null); \
   end


// M_RESIZE_QUEUE_OBJECT_COPY
// ------------------------

`define M_RESIZE_QUEUE_OBJECT_COPY(ARG, SIZE) \
   begin \
     while(ARG.size()>SIZE) void'(ARG.pop_front()); \
     while(ARG.size() != SIZE) ARG.push_back(null); \
   end

// m_ovm_record_array_int
// --------------------

`define m_ovm_record_array_int(ARG, RADIX, RECORDER) \
  begin \
    if(RECORDER.tr_handle != 0) begin\
      if(RADIX == OVM_ENUM) begin \
        if(!m_sc.array_warning_done) begin \
           m_sc.array_warning_done = 1; \
           ovm_object::m_sc.scratch1 = \
             `"Recording not supported for array enumerations: ARG`"; \
           _global_reporter.ovm_report_warning("RCDNTS", ovm_object::m_sc.scratch1, OVM_NONE); \
        end \
      end \
      else begin \
        for(int i__=0; i__<ARG.size(); ++i__) \
          RECORDER.record_field($psprintf(`"ARG[%0d]`",i__), ARG[i__], $bits(ARG[i__]), ovm_radix_enum'(RADIX)); \
      end \
    end \
  end


// m_ovm_record_qda_enum
// ---------------------

`define m_ovm_record_qda_enum(T, ARG, RECORDER) \
  begin \
    if(RECORDER.tr_handle != 0) begin\
      foreach(ARG[i__]) begin \
        T lh__=ARG[i__]; \
        RECORDER.record_string($psprintf(`"ARG[%0d]`",i__), lh__.name()); \
      end \
    end \
  end


// M_OVM_FIELD_DATA_ARRAY
// --------------------

`define M_OVM_FIELD_DATA_ARRAY(ARG,FLAG) \
   begin \
     case (what__) \
       OVM_COMPARE: \
         if ( !((FLAG)&OVM_NOCOMPARE) && (tmp_data__ != null) ) begin \
           int i__; \
           $cast(local_data__, tmp_data__); \
           if(ARG.size() != local_data__.ARG.size()) begin \
             int s1__, s2__; \
             m_sc.stringv = ""; \
             s1__ = ARG.size(); s2__ = local_data__.ARG.size(); \
             $swrite(m_sc.stringv, "lhs size = %0d : rhs size = %0d", s1__, s2__);\
             ovm_auto_options_object.comparer.print_msg(m_sc.stringv); \
           end \
           for(i__=0; i__<ARG.size() && i__<local_data__.ARG.size(); ++i__) begin \
             if(ARG[i__] !== local_data__.``ARG[i__]) begin \
               ovm_auto_options_object.comparer.scope.down_element(i__, null);\
               case(OVM_RADIX&(FLAG)) \
                 OVM_BIN: $swrite(m_sc.stringv, "lhs = 'b%0b : rhs = 'b%0b", \
                                ARG[i__], local_data__.ARG[i__]); \
                 OVM_OCT: $swrite(m_sc.stringv, "lhs = 'o%0o : rhs = 'o%0o", \
                                ARG[i__], local_data__.ARG[i__]); \
                 OVM_DEC: $swrite(m_sc.stringv, "lhs = %0d : rhs = %0d", \
                                ARG[i__], local_data__.ARG[i__]); \
                 OVM_UNSIGNED: $swrite(m_sc.stringv, "lhs = %0d : rhs = %0d", \
                                ARG[i__], local_data__.ARG[i__]); \
                 OVM_HEX: $swrite(m_sc.stringv, "lhs = 'h%0x : rhs = 'h%0x", \
                                ARG[i__], local_data__.ARG[i__]); \
                 OVM_STRING: $swrite(m_sc.stringv, "lhs = %0s : rhs = %0s", \
                                ARG[i__], local_data__.ARG[i__]); \
                 OVM_TIME: $swrite(m_sc.stringv, "lhs = %0t : rhs = %0t", \
                                ARG[i__], local_data__.ARG[i__]); \
                 default: $swrite(m_sc.stringv, "lhs = %0d : rhs = %0d", \
                                ARG[i__], local_data__.ARG[i__]); \
               endcase \
               ovm_auto_options_object.comparer.print_msg(m_sc.stringv); \
               ovm_auto_options_object.comparer.scope.up_element(null);\
             end \
           end \
         end \
       OVM_COPY: \
         if(!((FLAG)&OVM_NOCOPY) && (tmp_data__ != null)) \
          begin \
           int i__; \
           $cast(local_data__, tmp_data__); \
           /*Resizing of array is done in ovm_field*/ \
           for(i__=0; i__ < ARG``.size(); ++i__) begin \
             ARG[i__] = local_data__.``ARG[i__] ; \
           end \
         end \
       OVM_PRINT: \
         begin \
           if(((FLAG)&OVM_NOPRINT) == 0 && \
                          ovm_auto_options_object.printer.knobs.print_fields == 1) begin \
             `ovm_print_array_int3(ARG, ovm_radix_enum'((FLAG)&(OVM_RADIX)), \
                                   ovm_auto_options_object.printer) \
           end \
         end \
       OVM_RECORD: \
         begin \
           if(((FLAG)&OVM_NORECORD) == 0) begin \
             `m_ovm_record_array_int(ARG, ovm_radix_enum'((FLAG)&(OVM_RADIX)), \
                                   ovm_auto_options_object.recorder) \
           end \
         end \
     endcase \
   end

`define M_OVM_FIELD_ARRAY_INT_PACK(ARG,FLAG) \
   case(what__) \
      OVM_PACK: \
        if(((FLAG)&OVM_NOPACK) == 0) \
        begin \
          if((((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) || \
              (!((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) begin \
            if(ovm_auto_options_object.packer.use_metadata == 1) \
              ovm_auto_options_object.packer.pack_field_int(ARG.size(), 32); \
            foreach(ARG[i]) \
              ovm_auto_options_object.packer.pack_field(ARG[i], $bits(ARG[i])); \
          end \
        end \
      OVM_UNPACK: \
        if(((FLAG)&OVM_NOPACK) == 0) \
        begin \
          if((((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) || \
              (!((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) begin \
            if(ovm_auto_options_object.packer.use_metadata) begin \
              int s_; \
              s_ = ovm_auto_options_object.packer.unpack_field_int(32); \
              ARG = new[s_]; \
            end \
            foreach(ARG[i]) \
              ARG[i] = ovm_auto_options_object.packer.unpack_field($bits(ARG[i])); \
          end \
        end \
  endcase

`define M_OVM_FIELD_QUEUE_INT_PACK(ARG,FLAG) \
   case(what__) \
      OVM_PACK: \
        if(((FLAG)&OVM_NOPACK) == 0) \
        begin \
          if((((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) || \
              (!((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) begin \
            if(ovm_auto_options_object.packer.use_metadata == 1) \
              ovm_auto_options_object.packer.pack_field_int(ARG.size(), 32); \
            foreach(ARG[i]) \
              ovm_auto_options_object.packer.pack_field(ARG[i], $bits(ARG[i])); \
          end \
        end \
      OVM_UNPACK: \
        if(((FLAG)&OVM_NOPACK) == 0) \
        begin \
          if((((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) || \
              (!((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) begin \
            if(ovm_auto_options_object.packer.use_metadata) begin \
              int s_; \
              s_ = ovm_auto_options_object.packer.unpack_field_int(32); \
              while(ARG.size() < s_) ARG.push_back(0); \
              while(ARG.size() > s_) void'(ARG.pop_front()); \
            end \
            foreach(ARG[i]) \
              ARG[i] = ovm_auto_options_object.packer.unpack_field($bits(ARG[i])); \
          end \
        end \
  endcase

`define M_OVM_FIELD_DATA_SARRAY(ARG,FLAG) \
  begin \
    if((what__ & (FLAG)) || (what__ >= OVM_MACRO_EXTRAS)) begin \
      if(what__ == OVM_PRINT && ((FLAG)&OVM_NOPRINT) == 0) \
        `ovm_print_sarray_int3(ARG, ovm_radix_enum'((FLAG)&(OVM_RADIX)), \
                                   ovm_auto_options_object.printer) \
      else if(tmp_data__!=null) begin \
        foreach(ARG[i__]) \
          if($cast(local_data__, tmp_data__)) begin \
            void'(m_do_data($psprintf(`"ARG[%0d]`",i__), ARG[i__], local_data__.ARG[i__], what__, $bits(ARG[i__]), FLAG)); \
          end \
      end \
      else begin \
        foreach(ARG[i__]) \
          if($cast(local_data__, tmp_data__)) begin \
            void'(m_do_data($psprintf(`"ARG[%0d]`",i__), ARG[i__], 0, what__, $bits(ARG[i__]), FLAG)); \
          end \
      end \
    end \
  end


// M_OVM_FIELD_DATA_ARRAY_OBJECT
// ---------------------------

// m_ovm_record_array_object
// --------------------

`define m_ovm_record_array_object(ARG, RECORDER) \
  begin \
    if(RECORDER.tr_handle != 0) begin\
      ovm_object obj__; \
      for(int i__=0; i__<ARG.size(); ++i__) begin \
        if($cast(obj__, ARG[i__]))\
          if(obj__ != null) begin \
            m_sc.scope.down_element(i__, null);\
            obj__.m_field_automation(null, what__, str__); \
            m_sc.scope.up_element(null);\
          end \
      end \
    end \
  end

`define M_OVM_FIELD_DATA_ARRAY_OBJECT(ARG,FLAG) \
   begin \
   if((what__ & (FLAG)) || (what__ >= OVM_MACRO_EXTRAS)) begin \
     ovm_object this_d__, from_d__; \
     case (what__) \
       OVM_COMPARE: \
         if ( !((FLAG)&OVM_NOCOMPARE) && (tmp_data__ != null)) begin \
           int i__; \
           ovm_recursion_policy_enum orig_policy; \
           orig_policy = ovm_auto_options_object.comparer.policy; \
           if(((FLAG)&OVM_REFERENCE) != 0) begin \
             ovm_auto_options_object.comparer.policy = OVM_REFERENCE; \
           end \
           $cast(local_data__, tmp_data__); \
           if(ARG.size() != local_data__.``ARG.size()) begin \
             int s1__, s2__; \
             m_sc.stringv = ""; \
             s1__ = ARG.size(); s2__ = local_data__.ARG.size(); \
             $swrite(m_sc.stringv, "lhs size = %0d : rhs size = %0d", s1__, s2__);\
             ovm_auto_options_object.comparer.print_msg(m_sc.stringv); \
           end \
           for(i__=0; i__<ARG.size() && i__<local_data__.ARG.size(); ++i__) \
             void'(ovm_auto_options_object.comparer.compare_object($psprintf(`"ARG[%0d]`",i__), ARG[i__], local_data__.ARG[i__])); \
           ovm_auto_options_object.comparer.policy = orig_policy; \
         end \
       OVM_COPY: \
         if(!((FLAG)&OVM_NOCOPY) && (tmp_data__ != null) ) \
          begin \
           int i__; \
           $cast(local_data__, tmp_data__); \
           /*Resizing of array is done in ovm_field_array* macro*/ \
           for(i__=0; i__ < ARG``.size(); ++i__) begin \
             `DOSHALLOWCOPY(ARG[i__], local_data__.ARG[i__], FLAG) \
             `DODEEPCOPY(ARG[i__], FLAG) \
           end \
         end \
       OVM_PRINT: \
           if((((FLAG)&OVM_NOPRINT) == 0) && \
              ovm_auto_options_object.printer.knobs.print_fields == 1) \
           begin \
             `ovm_print_array_object3(ARG, ovm_auto_options_object.printer,FLAG) \
           end \
       OVM_RECORD: \
         begin \
           if((((FLAG)&OVM_NORECORD) == 0) && (((FLAG)&OVM_SHALLOW) == 0)) begin \
             `m_ovm_record_array_object(ARG,ovm_auto_options_object.recorder) \
           end \
         end \
     endcase \
   end \
   end

`define M_OVM_FIELD_ARRAY_OBJ_PACK(ARG,FLAG) \
   case(what__) \
      OVM_PACK: \
        if(((FLAG)&OVM_NOPACK) == 0) \
        begin \
          if((((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) || \
              (!((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) begin \
            if(ovm_auto_options_object.packer.use_metadata == 1) \
              ovm_auto_options_object.packer.pack_field_int(ARG.size(), 32); \
            foreach(ARG[i]) begin \
              ovm_auto_options_object.packer.pack_object(ARG[i]); \
            end \
          end \
        end \
      OVM_UNPACK: \
        if(((FLAG)&OVM_NOPACK) == 0) \
        begin \
          if((((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) || \
              (!((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) begin \
            if(ovm_auto_options_object.packer.use_metadata) begin \
              int s_; \
              s_ = ovm_auto_options_object.packer.unpack_field_int(32); \
              if(ARG.size() < s_) \
                _global_reporter.ovm_report_error("OBJUPK", $psprintf(`"Array ARG cannot support the unpack operation, the unpack requires %0d elements, ARG has only %0d`", s_, ARG.size()), OVM_NONE); \
            end \
            foreach(ARG[i]) begin \
              ovm_auto_options_object.packer.unpack_object(ARG[i]); \
              if(ovm_auto_options_object.packer.use_metadata == 0 && ARG[i] == null) \
                return; \
            end \
          end \
        end \
  endcase

`define M_OVM_FIELD_QUEUE_OBJ_PACK(ARG,FLAG) \
   case(what__) \
      OVM_PACK: \
        if(((FLAG)&OVM_NOPACK) == 0) \
        begin \
          if((((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) || \
              (!((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) begin \
            if(ovm_auto_options_object.packer.use_metadata == 1) \
              ovm_auto_options_object.packer.pack_field_int(ARG.size(), 32); \
            foreach(ARG[i]) begin \
              ovm_auto_options_object.packer.pack_object(ARG[i]); \
            end \
          end \
        end \
      OVM_UNPACK: \
        if(((FLAG)&OVM_NOPACK) == 0) \
        begin \
          if((((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) || \
              (!((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) begin \
            if(ovm_auto_options_object.packer.use_metadata) begin \
              int s_; \
              s_ = ovm_auto_options_object.packer.unpack_field_int(32); \
              if(ARG.size() < s_) \
                _global_reporter.ovm_report_error("OBJUPK", $psprintf(`"Queue ARG cannot support the unpack operation, the unpack requires %0d elements, ARG has only %0d`", s_, ARG.size()), OVM_NONE); \
            end \
            foreach(ARG[i]) begin \
              ovm_auto_options_object.packer.unpack_object(ARG[i]); \
              if(ovm_auto_options_object.packer.use_metadata == 0 && ARG[i] == null) \
                return; \
            end \
//          while(ARG.size() < s_) ARG.push_back(null); \
//          while(ARG.size() > s_) void'(ARG.pop_front()); \
//          foreach(ARG[i]) begin \
//            if(!ovm_auto_options_object.packer.is_null()) ARG[i] = new; \
//            ovm_auto_options_object.packer.unpack_object(ARG[i]); \
//          end \
          end \
        end \
  endcase

`define M_OVM_FIELD_DATA_SARRAY_OBJECT(ARG,FLAG) \
  begin \
    if((what__ & (FLAG)) || (what__ >= OVM_MACRO_EXTRAS)) begin \
      ovm_object lhs__; \
      if(what__ == OVM_PRINT && ((FLAG)&OVM_NOPRINT) == 0) \
        `ovm_print_sarray_object3(ARG, ovm_auto_options_object.printer, FLAG) \
      else if((what__ == OVM_COPY) && ((FLAG)&OVM_NOCOPY)==0) begin \
        $cast(local_data__, tmp_data__); \
        foreach(ARG[i__]) begin \
          if(local_data__.ARG[i__] == null || (((FLAG)&OVM_REFERENCE) != 0)) \
            ARG[i__] = local_data__.ARG[i__]; \
          else if(((FLAG)&OVM_SHALLOW) != 0) \
            ARG[i__] = new local_data__.ARG[i__]; \
          else if(ARG[i__] != null) \
            ARG[i__].copy(local_data__.ARG[i__]); \
          else \
            $cast(ARG[i__],local_data__.ARG[i__].clone()); \
        end \
      end \
      else if((what__ != OVM_COPY) && (tmp_data__!=null)) begin \
        $cast(local_data__, tmp_data__); \
        foreach(ARG[i__]) begin \
          lhs__ = ARG[i__]; \
          if($cast(local_data__, tmp_data__)) \
            void'(m_do_data_object($psprintf(`"ARG[%0d]`",i__), lhs__, local_data__.ARG[i__], what__, FLAG)); \
          else \
            void'(m_do_data_object($psprintf(`"ARG[%0d]`",i__), lhs__, null, what__, FLAG)); \
        end \
      end \
      else if (what__ != OVM_COPY) begin \
        foreach(ARG[i__]) begin \
          lhs__ = ARG[i__]; \
          void'(m_do_data_object($psprintf(`"ARG[%0d]`",i__), lhs__, null, what__, FLAG)); \
        end \
      end \
    end \
  end


// M_OVM_FIELD_DATA_ARRAY_STRING
// ---------------------------

// m_ovm_record_array_string
// ------------------------

`define m_ovm_record_array_string(ARG, RECORDER) \
  begin \
    if(RECORDER.tr_handle != 0) begin\
      for(int i__=0; i__<ARG.size(); ++i__) \
        RECORDER.record_string($psprintf(`"ARG[%0d]`", i__), ARG[i__]); \
    end \
  end

`define M_OVM_FIELD_DATA_ARRAY_STRING(ARG,FLAG) \
   begin \
   if((what__ & (FLAG)) || (what__ >= OVM_MACRO_EXTRAS)) begin \
     case (what__) \
       OVM_COMPARE: \
         if ( !((FLAG)&OVM_NOCOMPARE) && (tmp_data__ != null) ) begin \
           int i__; \
           $cast(local_data__, tmp_data__); \
           if(ARG.size() != local_data__.``ARG.size()) begin \
             int s1__, s2__; \
             m_sc.stringv = ""; \
             s1__ = ARG.size(); s2__ = local_data__.ARG.size(); \
             $swrite(m_sc.stringv, "lhs size = %0d : rhs size = %0d", s1__, s2__);\
             ovm_auto_options_object.comparer.print_msg(m_sc.stringv); \
           end \
           for(i__=0; i__<ARG.size() && i__<local_data__.ARG.size(); ++i__) \
             if(ARG[i__] != local_data__.ARG[i__]) begin \
               string ls__, rs__; \
               ls__ = ARG[i__]; rs__ = local_data__.ARG[i__]; \
               ovm_auto_options_object.comparer.scope.down_element(i__, null);\
               $swrite(m_sc.stringv, "lhs = %0s : rhs = %0s", ls__, rs__); \
               ovm_auto_options_object.comparer.print_msg(m_sc.stringv); \
               ovm_auto_options_object.comparer.scope.up_element(null);\
             end \
         end \
       OVM_COPY: \
         if(!((FLAG)&OVM_NOCOPY) && (tmp_data__ != null) ) \
          begin \
           int i__; \
           $cast(local_data__, tmp_data__); \
           /*Resizing of array is done in ovm_field_array* macro*/ \
           for(i__=0; i__ < ARG.size(); ++i__) \
             ARG[i__] = local_data__.ARG[i__] ; \
         end \
       OVM_PRINT: \
         begin \
           if((FLAG)&OVM_NOPRINT != 0 && \
                          ovm_auto_options_object.printer.knobs.print_fields == 1) \
             `ovm_print_array_string2(ARG, ovm_auto_options_object.printer) \
         end \
       OVM_RECORD: \
         begin \
           if(((FLAG)&OVM_NORECORD) == 0 && !m_sc.array_warning_done) begin \
             `m_ovm_record_array_string(ARG, ovm_auto_options_object.recorder) \
           end \
         end \
     endcase \
   end \
   end 

`define M_OVM_FIELD_DATA_SARRAY_STRING(ARG,FLAG) \
  begin \
    if((what__ & (FLAG)) || (what__ >= OVM_MACRO_EXTRAS)) begin \
      if(what__ == OVM_PRINT && ((FLAG)&OVM_NOPRINT) == 0) \
        `ovm_print_sarray_string2(ARG, ovm_auto_options_object.printer) \
      else if(tmp_data__!=null) begin \
        foreach(ARG[i__]) \
          if($cast(local_data__, tmp_data__)) begin \
            void'(m_do_data_string($psprintf(`"ARG[%0d]`",i__), ARG[i__], local_data__.ARG[i__], what__, FLAG)); \
          end \
      end \
      else begin \
        foreach(ARG[i__]) \
          if($cast(local_data__, tmp_data__)) begin \
            void'(m_do_data_string($psprintf(`"ARG[%0d]`",i__), ARG[i__], "", what__, FLAG)); \
          end \
      end \
    end \
  end

`define M_OVM_FIELD_ARRAY_STR_PACK(ARG,FLAG) \
   case(what__) \
      OVM_PACK: \
        if(((FLAG)&OVM_NOPACK) == 0) \
        begin \
          if((((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) || \
              (!((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) begin \
            if(ovm_auto_options_object.packer.use_metadata == 1) \
              ovm_auto_options_object.packer.pack_field_int(ARG.size(), 32); \
            foreach(ARG[i]) \
              ovm_auto_options_object.packer.pack_string(ARG[i]); \
          end \
        end \
      OVM_UNPACK: \
        if(((FLAG)&OVM_NOPACK) == 0) \
        begin \
          if((((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) || \
              (!((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) begin \
            if(ovm_auto_options_object.packer.use_metadata) begin \
              int s_; \
              s_ = ovm_auto_options_object.packer.unpack_field_int(32); \
              ARG = new[s_]; \
            end \
            foreach(ARG[i]) begin \
              ARG[i] = ovm_auto_options_object.packer.unpack_string(-1); \
            end \
          end \
        end \
  endcase

`define M_OVM_FIELD_QUEUE_STR_PACK(ARG,FLAG) \
   case(what__) \
      OVM_PACK: \
        if(((FLAG)&OVM_NOPACK) == 0) \
        begin \
          if((((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) || \
              (!((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) begin \
            if(ovm_auto_options_object.packer.use_metadata == 1) \
              ovm_auto_options_object.packer.pack_field_int(ARG.size(), 32); \
            foreach(ARG[i]) \
              ovm_auto_options_object.packer.pack_string(ARG[i]); \
          end \
        end \
      OVM_UNPACK: \
        if(((FLAG)&OVM_NOPACK) == 0) \
        begin \
          if((((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.abstract) || \
              (!((FLAG)&OVM_ABSTRACT) && ovm_auto_options_object.packer.physical)) begin \
            if(ovm_auto_options_object.packer.use_metadata) begin \
              int s_; \
              s_ = ovm_auto_options_object.packer.unpack_field_int(32); \
              while(ARG.size() < s_) ARG.push_back(""); \
              while(ARG.size() > s_) void'(ARG.pop_front()); \
            end \
            foreach(ARG[i]) begin \
              ARG[i] = ovm_auto_options_object.packer.unpack_string(-1); \
            end \
          end \
        end \
  endcase

// OVM_COMPARE_FIELD
// -----------------

`define OVM_COMPARE_FAILED(ARG) \
begin \
  ovm_object::m_sc.scratch1 = `"Compare failed ARG`"; \
   ovm_auto_options_object.comparer.result++; \
   if(ovm_auto_options_object.comparer.result <=  \
      ovm_auto_options_object.comparer.show_max) \
   begin \
     ovm_object::m_sc.scratch1 = `"Miscompare for field ARG`"; \
     _global_reporter.ovm_report_info("MISCMP", ovm_object::m_sc.scratch1, OVM_MEDIUM) \
   end \
end


// M_OVM_FIELD_DATA_AA_generic
// -------------------------

`define M_OVM_FIELD_DATA_AA_generic(TYPE, KEY, ARG, FLAG) \
  begin \
    if((what__ & (FLAG)) || (what__ >= OVM_MACRO_EXTRAS)) begin \
      case (what__) \
        OVM_COMPARE: \
           begin \
            if(!((FLAG)&OVM_NOCOMPARE) && (tmp_data__ != null) ) \
            begin \
              $cast(local_data__, tmp_data__); \
              if(ARG.num() != local_data__.ARG.num()) begin \
                 int s1__, s2__; \
                 m_sc.stringv = ""; \
                 s1__ = ARG.num(); s2__ = local_data__.ARG.num(); \
                 $swrite(m_sc.stringv, "lhs size = %0d : rhs size = %0d", \
                    s1__, s2__);\
                 ovm_auto_options_object.comparer.print_msg(m_sc.stringv); \
              end \
              string_aa_key = ""; \
              while(ARG.next(string_aa_key)) begin \
                ovm_auto_options_object.comparer.scope.set_arg({"[",string_aa_key,"]"}); \
                void'(m_do_data({`"ARG[`", string_aa_key, "]"}, \
                    ARG[string_aa_key], \
                    local_data__.ARG[string_aa_key], what__, \
                    $bits(ARG[string_aa_key]), FLAG)); \
                ovm_auto_options_object.comparer.scope.unset_arg(string_aa_key); \
              end \
            end \
           end \
        OVM_COPY: \
          begin \
            if(!((FLAG)&OVM_NOCOPY) && (tmp_data__ != null) ) \
            begin \
              $cast(local_data__, tmp_data__); \
              ARG.delete(); \
              string_aa_key = ""; \
              while(local_data__.ARG.next(string_aa_key)) \
                ARG[string_aa_key] = local_data__.ARG[string_aa_key]; \
            end \
          end \
        OVM_PRINT: \
          `ovm_print_aa_``KEY``_``TYPE``3(ARG, ovm_radix_enum'((FLAG)&(OVM_RADIX)), \
             ovm_auto_options_object.printer) \
      endcase \
    end \
  end


// M_OVM_FIELD_DATA_AA_int_string
// ----------------------------

`define M_OVM_FIELD_DATA_AA_int_string(ARG, FLAG) \
  `M_OVM_FIELD_DATA_AA_generic(int, string, ARG, FLAG)

// M_OVM_FIELD_DATA_AA_int_int
// ----------------------------

`define M_OVM_FIELD_DATA_AA_int_key(KEY, ARG, FLAG) \
  begin \
    if((what__ & (FLAG)) || (what__ >= OVM_MACRO_EXTRAS)) begin \
      KEY aa_key; \
      case (what__) \
        OVM_COMPARE: \
           begin \
            if(!((FLAG)&OVM_NOCOMPARE) && (tmp_data__ != null) ) \
            begin \
              $cast(local_data__, tmp_data__); \
              if(ARG.num() != local_data__.ARG.num()) begin \
                 int s1__, s2__; \
                 m_sc.stringv = ""; \
                 s1__ = ARG.num(); s2__ = local_data__.ARG.num(); \
                 $swrite(m_sc.stringv, "lhs size = %0d : rhs size = %0d", \
                    s1__, s2__);\
                 ovm_auto_options_object.comparer.print_msg(m_sc.stringv); \
              end \
              ovm_auto_options_object.comparer.scope.up(null); \
              if(ARG.first(aa_key)) \
                do begin \
                  $swrite(string_aa_key, "%0d", aa_key); \
                  ovm_auto_options_object.comparer.scope.set_arg({"[",string_aa_key,"]"}); \
                  void'(m_do_data({`"ARG[`", string_aa_key, "]"}, \
                    ARG[aa_key], \
                    local_data__.ARG[aa_key], what__, \
                    $bits(ARG[aa_key]), FLAG)); \
                  ovm_auto_options_object.comparer.scope.unset_arg(string_aa_key); \
                end while(ARG.next(aa_key)); \
              ovm_auto_options_object.comparer.scope.down(`"ARG`",null); \
            end \
           end \
        OVM_COPY: \
          begin \
            if(!((FLAG)&OVM_NOCOPY) && (tmp_data__ != null) ) \
            begin \
              $cast(local_data__, tmp_data__); \
              ARG.delete(); \
              if(local_data__.ARG.first(aa_key)) \
                do begin \
                  ARG[aa_key] = local_data__.ARG[aa_key]; \
                end while(local_data__.ARG.next(aa_key)); \
            end \
          end \
        OVM_PRINT: \
          `ovm_print_aa_int_key4(KEY,ARG, ovm_radix_enum'((FLAG)&(OVM_RADIX)), \
             ovm_auto_options_object.printer) \
      endcase \
    end \
  end


// M_OVM_FIELD_DATA_AA_enum_key
// ----------------------------

`define M_OVM_FIELD_DATA_AA_enum_key(KEY, ARG, FLAG) \
  begin \
    if((what__ & (FLAG)) || (what__ >= OVM_MACRO_EXTRAS)) begin \
      KEY aa_key; \
      case (what__) \
        OVM_COMPARE: \
           begin \
            if(!((FLAG)&OVM_NOCOMPARE) && (tmp_data__ != null) ) \
            begin \
              $cast(local_data__, tmp_data__); \
              if(ARG.num() != local_data__.ARG.num()) begin \
                 int s1__, s2__; \
                 m_sc.stringv = ""; \
                 s1__ = ARG.num(); s2__ = local_data__.ARG.num(); \
                 $swrite(m_sc.stringv, "lhs size = %0d : rhs size = %0d", \
                    s1__, s2__);\
                 ovm_auto_options_object.comparer.print_msg(m_sc.stringv); \
              end \
              ovm_auto_options_object.comparer.scope.up(null); \
              if(ARG.first(aa_key)) \
                do begin \
                  void'(ovm_auto_options_object.comparer.compare_field_int({`"ARG[`",aa_key.name(),"]"}, \
                    ARG[aa_key], local_data__.ARG[aa_key], $bits(ARG[aa_key]), \
                    ovm_radix_enum'((FLAG)&OVM_RADIX) )); \
                end while(ARG.next(aa_key)); \
              ovm_auto_options_object.comparer.scope.down(`"ARG`",null); \
            end \
           end \
        OVM_COPY: \
          begin \
            if(!((FLAG)&OVM_NOCOPY) && (tmp_data__ != null) ) \
            begin \
              $cast(local_data__, tmp_data__); \
              ARG.delete(); \
              if(local_data__.ARG.first(aa_key)) \
                do begin \
                  ARG[aa_key] = local_data__.ARG[aa_key]; \
                end while(local_data__.ARG.next(aa_key)); \
            end \
          end \
        OVM_PRINT: \
          begin \
            ovm_printer p__ = ovm_auto_options_object.printer; \
            p__.print_array_header (`"ARG`", ARG.num(),`"aa_``KEY`"); \
            if((p__.knobs.depth == -1) || (p__.m_scope.depth() < p__.knobs.depth+1)) \
            begin \
              if(ARG.first(aa_key)) \
                do begin \
                  ovm_auto_options_object.printer.print_field( \
                    {"[",aa_key.name(),"]"}, ARG[aa_key], $bits(ARG[aa_key]), \
                    ovm_radix_enum'((FLAG)&OVM_RADIX), "[" ); \
                end while(ARG.next(aa_key)); \
            end \
            p__.print_array_footer(ARG.num()); \
            p__.print_footer(); \
          end \
      endcase \
    end \
  end 

// M_OVM_FIELD_DATA_AA_object_string
// -------------------------------

`define M_OVM_FIELD_DATA_AA_object_string(ARG, FLAG) \
  begin \
    if((what__ & (FLAG)) || (what__ >= OVM_MACRO_EXTRAS)) begin \
      case (what__) \
        OVM_COMPARE: \
           begin \
            if(!((FLAG)&OVM_NOCOMPARE) && (tmp_data__ != null) ) \
            begin \
              $cast(local_data__, tmp_data__); \
              if(ARG.num() != local_data__.ARG.num()) begin \
                 int s1__, s2__; \
                 m_sc.stringv = ""; \
                 s1__ = ARG.num(); s2__ = local_data__.ARG.num(); \
                 $swrite(m_sc.stringv, "lhs size = %0d : rhs size = %0d", \
                          s1__, s2__);\
                 ovm_auto_options_object.comparer.print_msg(m_sc.stringv); \
              end \
              string_aa_key = ""; \
              while(ARG.next(string_aa_key)) begin \
                ovm_object tmp; \
                /* Since m_do_data_object is inout, need a ovm_object for */ \
                /* assignment compatibility. We must cast back the return. */ \
                tmp = ARG[string_aa_key]; \
                ovm_auto_options_object.comparer.scope.down({"[",string_aa_key,"]"},tmp); \
                void'(m_do_data_object({"[", string_aa_key, "]"}, tmp, \
                    local_data__.ARG[string_aa_key], what__, FLAG)); \
                ovm_auto_options_object.comparer.scope.up(tmp,"["); \
              end \
            end \
          end \
        OVM_COPY: \
          begin \
           if(!((FLAG)&OVM_NOCOPY) && (tmp_data__ != null) ) \
           begin \
            $cast(local_data__, tmp_data__); \
            ARG.delete(); \
            if(local_data__.ARG.first(string_aa_key)) \
             do \
               if((FLAG)&OVM_REFERENCE) \
                ARG[string_aa_key] = local_data__.ARG[string_aa_key]; \
             /*else if((FLAG)&OVM_SHALLOW)*/ \
             /* ARG[string_aa_key] = new local_data__.ARG[string_aa_key];*/ \
               else begin\
                $cast(ARG[string_aa_key],local_data__.ARG[string_aa_key].clone());\
                ARG[string_aa_key].set_name({`"ARG`","[",string_aa_key, "]"});\
               end \
             while(local_data__.ARG.next(string_aa_key)); \
           end \
          end \
        OVM_PRINT: \
          `ovm_print_aa_string_object3(ARG, ovm_auto_options_object.printer,FLAG) \
      endcase \
    end \
  end

// M_OVM_FIELD_DATA_AA_object_int
// -------------------------------

`define M_OVM_FIELD_DATA_AA_object_int(ARG, FLAG) \
  begin \
    int key__; \
    if((what__ & (FLAG)) || (what__ >= OVM_MACRO_EXTRAS)) begin \
      case (what__) \
        OVM_COMPARE: \
           begin \
            if(!((FLAG)&OVM_NOCOMPARE) && (tmp_data__ != null) ) \
            begin \
              $cast(local_data__, tmp_data__); \
              if(ARG.num() != local_data__.ARG.num()) begin \
                 int s1__, s2__; \
                 m_sc.stringv = ""; \
                 s1__ = ARG.num(); s2__ = local_data__.ARG.num(); \
                 $swrite(m_sc.stringv, "lhs size = %0d : rhs size = %0d", \
                          s1__, s2__);\
                 ovm_auto_options_object.comparer.print_msg(m_sc.stringv); \
              end \
              if(ARG.first(key__)) begin \
                do begin \
                  ovm_object tmp__; \
                  /* Since m_do_data_object is inout, need a ovm_object for */ \
                  /* assignment compatibility. We must cast back the return. */ \
                  tmp__ = ARG[key__]; \
                  $swrite(m_sc.stringv, "[%0d]", key__); \
                  ovm_auto_options_object.comparer.scope.down_element(key__,tmp__); \
                  void'(m_do_data_object(m_sc.stringv, tmp__, \
                      local_data__.ARG[key__], what__, FLAG)); \
                  ovm_auto_options_object.comparer.scope.up_element(tmp__); \
                end while(ARG.next(key__)); \
              end \
            end \
          end \
        OVM_COPY: \
          begin \
           if(!((FLAG)&OVM_NOCOPY) && (tmp_data__ != null) ) \
           begin \
            $cast(local_data__, tmp_data__); \
            ARG.delete(); \
            if(local_data__.ARG.first(key__)) \
             do begin \
               if((FLAG)&OVM_REFERENCE) \
                ARG[key__] = local_data__.ARG[key__]; \
             /*else if((FLAG)&OVM_SHALLOW)*/ \
             /* ARG[key__] = new local_data__.ARG[key__];*/ \
               else begin\
                 ovm_object tmp_obj; \
                 tmp_obj = local_data__.ARG[key__].clone(); \
                 if(tmp_obj != null) \
                   $cast(ARG[key__], tmp_obj); \
                 else \
                   ARG[key__]=null; \
               end \
             end while(local_data__.ARG.next(key__)); \
           end \
         end \
        OVM_PRINT: \
          `ovm_print_aa_int_object3(ARG, ovm_auto_options_object.printer,FLAG) \
      endcase \
    end \
  end

// M_OVM_FIELD_DATA_AA_string_string
// -------------------------------

`define M_OVM_FIELD_DATA_AA_string_string(ARG, FLAG) \
  begin \
    if((what__ & (FLAG)) || (what__ >= OVM_MACRO_EXTRAS)) begin \
      case (what__) \
        OVM_COMPARE: \
           begin \
            if(!((FLAG)&OVM_NOCOMPARE) && (tmp_data__ != null) ) \
            begin \
              $cast(local_data__, tmp_data__); \
              if(ARG.num() != local_data__.ARG.num()) begin \
                 int s1__, s2__; \
                 m_sc.stringv = ""; \
                 s1__ = ARG.num(); s2__ = local_data__.ARG.num(); \
                 $swrite(m_sc.stringv, "lhs size = %0d : rhs size = %0d", \
                    s1__, s2__);\
                 ovm_auto_options_object.comparer.print_msg(m_sc.stringv); \
              end \
              string_aa_key = ""; \
              while(ARG.next(string_aa_key)) begin \
                ovm_auto_options_object.comparer.scope.set_arg({"[",string_aa_key,"]"}); \
                void'(m_do_data_string({`"ARG[`", string_aa_key, "]"}, \
                    ARG[string_aa_key], \
                    local_data__.ARG[string_aa_key], what__, FLAG) ); \
                ovm_auto_options_object.comparer.scope.unset_arg(string_aa_key); \
              end \
            end \
           end \
        OVM_COPY: \
          begin \
            if(!((FLAG)&OVM_NOCOPY) && (local_data__ !=null)) \
            begin \
              ARG.delete(); \
              string_aa_key = ""; \
              while(local_data__.ARG.next(string_aa_key)) \
                ARG[string_aa_key] = local_data__.ARG[string_aa_key]; \
            end \
          end \
        OVM_PRINT: \
          `ovm_print_aa_string_string2(ARG, ovm_auto_options_object.printer) \
      endcase \
    end \
  end


// DOREFERENCECOPY
// ---------------

`define DOREFERENCECOPY(ARG,FLAG) \
  if( (FLAG)&OVM_REFERENCE)) \
      ARG = local_data__.``ARG; \

// DODEEPCOPY
// ----------

`define DODEEPCOPY(ARG,FLAG) \
  begin \
    ovm_object this_d__, from_d__; \
    if(tmp_data__ != null) \
      if(!$cast(local_data__, tmp_data__)) begin \
        ovm_object::m_sc.scratch1 = `"Cast failed for argument: ARG`"; \
      end \
    if(ARG != null) $cast(this_d__,ARG); \
    if(local_data__.ARG != null) $cast(from_d__,local_data__.ARG); \
\
    if((this_d__==null) && (from_d__!=null)) begin \
      this_d__ = from_d__.clone(); \
      this_d__.set_name(`"ARG`"); \
    end \
    else if(from_d__ == null) \
      this_d__ = from_d__; \
    else begin \
      this_d__.copy(from_d__); \
    end \
    if((this_d__ == null) || !$cast(ARG, this_d__)) begin \
      ovm_object::m_sc.scratch1 = `"Cast failed for ARG during copy`"; \
      _global_reporter.ovm_report_error("CSTFLD", ovm_object::m_sc.scratch1, OVM_NONE); \
    end \
  end    


// DOSHALLOWCOPY
// -------------

`define DOSHALLOWCOPY(ARG1,ARG2,FLAG) \
  if( (FLAG)&OVM_SHALLOW) \
    begin \
      ovm_object lhs__, rhs__; \
      ovm_object::m_sc.scratch1 = `"Executing shallow copy of arg ARG`"; \
/* Can't do shallow copy right now due to an issue with abstract classes */ \
/* like ovm_object, so do a deep copy instead. */ \
      if(ARG2==null) ARG1 = ARG2; \
      else begin \
        if(ARG1 != null) $cast(lhs__, ARG1); \
        if(ARG2 != null) $cast(rhs__, ARG2); \
        if(rhs__!=null && lhs__!=null) \
          lhs__.copy(rhs__); \
        else if(rhs__ != null) begin \
          $cast(lhs__, rhs__.clone()); \
          if (lhs__ != null) \
            $cast(ARG1, lhs__); \
        end \
        else \
          ARG1 = null; \
/*          ARG = new local_data__.ARG; */ \
      end \
    end \
  else \
    begin \
      ovm_object::m_sc.scratch1 = `"Shallow copy off for arg ARG`"; \
    end 


// M_OVM_FIELD_SET
// ----------------

`define M_OVM_FIELD_SET(ARG,FLAG) \
  void'(ovm_object::m_do_set (str__, `"ARG`", ARG, what__, FLAG)); \


// M_OVM_FIELD_SET_EVENT
// ----------------------

`define M_OVM_FIELD_SET_EVENT(ARG,FLAG) \
  /*Not implemented*/


// M_OVM_FIELD_SET_OBJECT
// -----------------------

`define M_OVM_FIELD_SET_OBJECT(ARG,FLAG) \
  begin \
    ovm_object arg_obj__; \
    int r__; /*return 1 if get succeeds*/ \
    if(ARG != null) $cast(arg_obj__, ARG); \
    r__ = ovm_object::m_do_set_object(str__, `"ARG`", \
        arg_obj__, what__, FLAG); \
    /*in case of a set, cast back */ \
    if(r__ && (what__ == OVM_SETOBJ) && (arg_obj__ != null)) \
      $cast(ARG, arg_obj__); \
    else if(arg_obj__ == null) \
      ARG = null; \
  end


// M_OVM_FIELD_SET_STRING
// -----------------------

`define M_OVM_FIELD_SET_STRING(ARG,FLAG) \
  void'(ovm_object::m_do_set_string (str__, `"ARG`", ARG, what__, FLAG)); \

`define M_OVM_FIELD_SET_QUEUE_TYPE(ATYPE, ARRAY, RHS, FLAG) \
  if((what__ >= OVM_START_FUNCS && what__ <= OVM_END_FUNCS) && (((FLAG)&OVM_READONLY) == 0)) begin \
    bit wildcard_index__; \
    int index__; \
    index__ = ovm_get_array_index_int(str__, wildcard_index__); \
    if(what__==OVM_SET``ATYPE) \
    begin \
      if(ovm_is_array(str__)  && (index__ != -1)) begin\
        if(wildcard_index__) begin \
          for(index__=0; index__<ARRAY.size(); ++index__) begin \
            if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)})) begin \
              ARRAY[index__] = RHS; \
              m_sc.status = 1; \
            end \
          end \
        end \
        else if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)})) begin \
          ARRAY[index__] =  RHS; \
          m_sc.status = 1; \
        end \
      end \
    end \
 end

`define M_OVM_FIELD_SET_QUEUE_ENUM(T, ARRAY, RHS, FLAG) \
  if((what__ >= OVM_START_FUNCS && what__ <= OVM_END_FUNCS) && (((FLAG)&OVM_READONLY) == 0)) begin \
    bit wildcard_index__; \
    int index__; \
    index__ = ovm_get_array_index_int(str__, wildcard_index__); \
    if(what__==OVM_SETINT) \
    begin \
      if(ovm_is_array(str__)  && (index__ != -1)) begin\
        if(wildcard_index__) begin \
          for(index__=0; index__<ARRAY.size(); ++index__) begin \
            if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)})) begin \
              ARRAY[index__] = T'(RHS); \
              m_sc.status = 1; \
            end \
          end \
        end \
        else if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)})) begin \
          ARRAY[index__] =  T'(RHS); \
          m_sc.status = 1; \
        end \
      end \
    end \
 end

`define M_OVM_FIELD_SET_QUEUE_OBJECT_TYPE(ARRAY, FLAG) \
  if((what__ >= OVM_START_FUNCS && what__ <= OVM_END_FUNCS) && (((FLAG)&OVM_READONLY) == 0)) begin \
    bit wildcard_index__; \
    int index__; \
    index__ = ovm_get_array_index_int(str__, wildcard_index__); \
    if(what__==OVM_SETOBJ) \
    begin \
      if(ovm_is_array(str__) ) begin\
        if(wildcard_index__) begin \
          for(index__=0; index__<ARRAY.size(); ++index__) begin \
            if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)})) begin \
              if (m_sc.object != null) \
                $cast(ARRAY[index__], m_sc.object); \
              m_sc.status = 1; \
            end \
          end \
        end \
        else if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)})) begin \
          if (m_sc.object != null) \
            $cast(ARRAY[index__], m_sc.object); \
          m_sc.status = 1; \
        end \
      end \
    end \
 end

`define M_OVM_FIELD_SET_AA_TYPE(INDEX_TYPE, ARRAY_TYPE, ARRAY, RHS, FLAG) \
  if((what__ >= OVM_START_FUNCS && what__ <= OVM_END_FUNCS) && (((FLAG)&OVM_READONLY) == 0)) begin \
    bit wildcard_index__; \
    INDEX_TYPE index__; \
    index__ = ovm_get_array_index_``INDEX_TYPE(str__, wildcard_index__); \
    if(what__==OVM_SET``ARRAY_TYPE) \
    begin \
      if(ovm_is_array(str__) ) begin\
        if(wildcard_index__) begin \
          if(ARRAY.first(index__)) \
          do begin \
            if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)}) ||  \
               ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0s]", index__)})) begin \
              ARRAY[index__] = RHS; \
              m_sc.status = 1; \
            end \
          end while(ARRAY.next(index__));\
        end \
        else if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)})) begin \
          ARRAY[index__] = RHS; \
          m_sc.status = 1; \
        end \
        else if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0s]", index__)})) begin \
          ARRAY[index__] = RHS; \
          m_sc.status = 1; \
        end \
      end \
    end \
 end

`define M_OVM_FIELD_SET_AA_OBJECT_TYPE(INDEX_TYPE, ARRAY, FLAG) \
  if((what__ >= OVM_START_FUNCS && what__ <= OVM_END_FUNCS) && (((FLAG)&OVM_READONLY) == 0)) begin \
    bit wildcard_index__; \
    INDEX_TYPE index__; \
    index__ = ovm_get_array_index_``INDEX_TYPE(str__, wildcard_index__); \
    if(what__==OVM_SETOBJ) \
    begin \
      if(ovm_is_array(str__) ) begin\
        if(wildcard_index__) begin \
          if(ARRAY.first(index__)) \
          do begin \
            if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)}) || \
               ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0s]", index__)})) begin \
              if (m_sc.object != null) \
                $cast(ARRAY[index__], m_sc.object); \
              m_sc.status = 1; \
            end \
          end while(ARRAY.next(index__));\
        end \
        else if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)})) begin \
          if (m_sc.object != null) \
            $cast(ARRAY[index__], m_sc.object); \
          m_sc.status = 1; \
        end \
        else if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0s]", index__)})) begin \
          if (m_sc.object != null) \
            $cast(ARRAY[index__], m_sc.object); \
          m_sc.status = 1; \
        end \
      end \
    end \
 end

`define M_OVM_FIELD_SET_AA_INT_TYPE(INDEX_TYPE, ARRAY_TYPE, ARRAY, RHS, FLAG) \
  if((what__ >= OVM_START_FUNCS && what__ <= OVM_END_FUNCS) && (((FLAG)&OVM_READONLY) == 0)) begin \
    bit wildcard_index__; \
    INDEX_TYPE index__; \
    string idx__; \
    index__ = ovm_get_array_index_int(str__, wildcard_index__); \
    if(what__==OVM_SET``ARRAY_TYPE) \
    begin \
      if(ovm_is_array(str__) ) begin\
        if(wildcard_index__) begin \
          if(ARRAY.first(index__)) \
          do begin \
            $swrite(idx__, m_sc.scope.get_arg(), "[", index__, "]"); \
            if(ovm_is_match(str__, idx__)) begin \
              ARRAY[index__] = RHS; \
              m_sc.status = 1; \
            end \
          end while(ARRAY.next(index__));\
        end \
        else if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)})) begin \
          ARRAY[index__] = RHS; \
          m_sc.status = 1; \
        end  \
      end \
    end \
 end


`define M_OVM_FIELD_SET_AA_INT_ENUMTYPE(INDEX_TYPE, ARRAY_TYPE, ARRAY, RHS, FLAG) \
  if((what__ >= OVM_START_FUNCS && what__ <= OVM_END_FUNCS) && (((FLAG)&OVM_READONLY) == 0)) begin \
    bit wildcard_index__; \
    INDEX_TYPE index__; \
    string idx__; \
    index__ = INDEX_TYPE'(ovm_get_array_index_int(str__, wildcard_index__)); \
    if(what__==OVM_SET``ARRAY_TYPE) \
    begin \
      if(ovm_is_array(str__) ) begin\
        if(wildcard_index__) begin \
          if(ARRAY.first(index__)) \
          do begin \
            $swrite(idx__, m_sc.scope.get_arg(), "[", index__, "]"); \
            if(ovm_is_match(str__, idx__)) begin \
              ARRAY[index__] = RHS; \
              m_sc.status = 1; \
            end \
          end while(ARRAY.next(index__));\
        end \
        else if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)})) begin \
          ARRAY[index__] = RHS; \
          m_sc.status = 1; \
        end  \
      end \
    end \
 end


`define M_OVM_FIELD_SET_ARRAY_TYPE(ARRAY_TYPE, ARRAY, RHS, FLAG) \
  if((what__ >= OVM_START_FUNCS && what__ <= OVM_END_FUNCS) && (((FLAG)&OVM_READONLY) == 0)) begin \
    int index__; \
    bit wildcard_index__; \
    index__ = ovm_get_array_index_int(str__, wildcard_index__); \
    if(what__==OVM_SET``ARRAY_TYPE) \
    begin \
      if(ovm_is_array(str__) ) begin\
        if(wildcard_index__) begin \
          for(int index__=0; index__<ARRAY.size(); ++index__) begin \
            if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)})) begin \
              ARRAY[index__] = RHS; \
              m_sc.status = 1; \
            end \
          end \
        end \
        else if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)})) begin \
          ARRAY[index__] = RHS; \
          m_sc.status = 1; \
        end \
        else if(what__==OVM_SET && ovm_is_match(str__, m_sc.scope.get_arg())) begin \
          int size__; \
          size__ = m_sc.bitstream; \
          ARRAY = new[size__](ARRAY); \
          m_sc.status = 1; \
        end \
      end \
      else if(what__==OVM_SET && ovm_is_match(str__, m_sc.scope.get_arg())) begin \
        int size__; \
        size__ = m_sc.bitstream; \
        ARRAY = new[size__](ARRAY); \
        m_sc.status = 1; \
      end \
    end \
    else if(what__==OVM_SET && ovm_is_match(str__, m_sc.scope.get_arg())) begin \
     int size__; \
     size__ = m_sc.bitstream; \
     ARRAY = new[size__](ARRAY); \
     m_sc.status = 1; \
    end \
 end

`define M_OVM_FIELD_SET_ARRAY_ENUM(T, ARRAY, RHS, FLAG) \
  if((what__ >= OVM_START_FUNCS && what__ <= OVM_END_FUNCS) && (((FLAG)&OVM_READONLY) == 0)) begin \
    int index__; \
    bit wildcard_index__; \
    index__ = ovm_get_array_index_int(str__, wildcard_index__); \
    if(what__==OVM_SETINT) \
    begin \
      if(ovm_is_array(str__) ) begin\
        if(wildcard_index__) begin \
          for(int index__=0; index__<ARRAY.size(); ++index__) begin \
            if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)})) begin \
              ARRAY[index__] = T'(RHS); \
              m_sc.status = 1; \
            end \
          end \
        end \
        else if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)})) begin \
          ARRAY[index__] = T'(RHS); \
          m_sc.status = 1; \
        end \
        else if(what__==OVM_SET && ovm_is_match(str__, m_sc.scope.get_arg())) begin \
          int size__; \
          size__ = m_sc.bitstream; \
          ARRAY = new[size__](ARRAY); \
          m_sc.status = 1; \
        end \
      end \
      else if(what__==OVM_SET && ovm_is_match(str__, m_sc.scope.get_arg())) begin \
        int size__; \
        size__ = m_sc.bitstream; \
        ARRAY = new[size__](ARRAY); \
        m_sc.status = 1; \
      end \
    end \
    else if(what__==OVM_SET && ovm_is_match(str__, m_sc.scope.get_arg())) begin \
     int size__; \
     size__ = m_sc.bitstream; \
     ARRAY = new[size__](ARRAY); \
     m_sc.status = 1; \
    end \
 end

`define M_OVM_FIELD_SET_SARRAY_TYPE(ARRAY_TYPE, ARRAY, RHS, FLAG) \
  if((what__ >= OVM_START_FUNCS && what__ <= OVM_END_FUNCS) && (((FLAG)&OVM_READONLY) == 0)) begin \
    int index__; \
    bit wildcard_index__; \
    index__ = ovm_get_array_index_int(str__, wildcard_index__); \
    if(what__==OVM_SET``ARRAY_TYPE) \
    begin \
      if(ovm_is_array(str__) ) begin\
        if(wildcard_index__) begin \
          foreach(ARRAY[index__]) begin \
            if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)})) begin \
              ARRAY[index__] = RHS; \
              m_sc.status = 1; \
            end \
          end \
        end \
        else if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)})) begin \
          ARRAY[index__] = RHS; \
          m_sc.status = 1; \
        end \
      end \
    end \
  end

`define M_OVM_FIELD_SET_SARRAY_ENUM(T, ARRAY, RHS, FLAG) \
  if((what__ >= OVM_START_FUNCS && what__ <= OVM_END_FUNCS) && (((FLAG)&OVM_READONLY) == 0)) begin \
    int index__; \
    bit wildcard_index__; \
    index__ = ovm_get_array_index_int(str__, wildcard_index__); \
    if(what__==OVM_SETINT) \
    begin \
      if(ovm_is_array(str__) ) begin\
        if(wildcard_index__) begin \
          foreach(ARRAY[index__]) begin \
            if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)})) begin \
              ARRAY[index__] = T'(RHS); \
              m_sc.status = 1; \
            end \
          end \
        end \
        else if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)})) begin \
          ARRAY[index__] = T'(RHS); \
          m_sc.status = 1; \
        end \
      end \
    end \
  end

`define M_OVM_FIELD_SET_ARRAY_OBJECT_TYPE(ARRAY, FLAG) \
  if((what__ >= OVM_START_FUNCS && what__ <= OVM_END_FUNCS) && (((FLAG)&OVM_READONLY) == 0)) begin \
    int index__; \
    bit wildcard_index__; \
    index__ = ovm_get_array_index_int(str__, wildcard_index__); \
    if(what__==OVM_SETOBJ) \
    begin \
      if(ovm_is_array(str__) ) begin\
        if(wildcard_index__) begin \
          for(int index__=0; index__<ARRAY.size(); ++index__) begin \
            if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)})) begin \
              if (m_sc.object != null) begin \
                $cast(ARRAY[index__], m_sc.object); \
              end \
              m_sc.status = 1; \
            end \
          end \
        end \
        else if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)})) begin \
          if (m_sc.object != null) begin \
            $cast(ARRAY[index__], m_sc.object); \
          end \
          m_sc.status = 1; \
        end \
      end \
    end \
    else if(what__==OVM_SET && !ovm_is_array(str__) && ovm_is_match(str__, m_sc.scope.get_arg())) begin \
     int size__; \
     size__ = m_sc.bitstream; \
     ARRAY = new[size__](ARRAY); \
     m_sc.status = 1; \
    end \
 end

`define M_OVM_FIELD_SET_SARRAY_OBJECT_TYPE(ARRAY, FLAG) \
  if((what__ >= OVM_START_FUNCS && what__ <= OVM_END_FUNCS) && (((FLAG)&OVM_READONLY) == 0)) begin \
    int index__; \
    bit wildcard_index__; \
    index__ = ovm_get_array_index_int(str__, wildcard_index__); \
    if(what__==OVM_SETOBJ) \
    begin \
      if(ovm_is_array(str__) ) begin\
        if(wildcard_index__) begin \
          foreach(ARRAY[index__]) begin \
            if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)})) begin \
              if (m_sc.object != null) begin \
                $cast(ARRAY[index__], m_sc.object); \
              end \
              else \
                ARRAY[index__] = null; \
              m_sc.status = 1; \
            end \
          end \
        end \
        else if(ovm_is_match(str__, {m_sc.scope.get_arg(),$psprintf("[%0d]", index__)})) begin \
          if (m_sc.object != null) begin \
            $cast(ARRAY[index__], m_sc.object); \
          end \
          else \
            ARRAY[index__] = null; \
          m_sc.status = 1; \
        end \
      end \
    end \
  end 

// M_OVM_FIELD_SET_ARRAY_OBJECT
// -----------------------------

// The cast to ovm_object allows these macros to work
// with ARG base types not derived from ovm_object.

`define M_OVM_FIELD_SET_ARRAY_OBJECT(ARG,FLAG) \
  `M_OVM_FIELD_SET_ARRAY_OBJECT_TYPE(ARG, FLAG) \
  if((what__ >= OVM_START_FUNCS && what__ <= OVM_END_FUNCS) && (((FLAG)&OVM_READONLY) == 0)) begin \
    ovm_object obj__; \
    for(int index__=0; index__<ARG.size(); ++index__) begin \
       if($cast(obj__,ARG[index__]) && (obj__!=null)) \
          obj__.m_field_automation(null, what__, str__); \
    end \
  end

`define M_OVM_FIELD_SET_SARRAY_OBJECT(ARG,FLAG) \
  `M_OVM_FIELD_SET_SARRAY_OBJECT_TYPE(ARG, FLAG) \
  if((what__ >= OVM_START_FUNCS && what__ <= OVM_END_FUNCS) && (((FLAG)&OVM_READONLY) == 0)) begin \
    ovm_object obj__; \
    foreach(ARG[index__]) begin \
       if($cast(obj__,ARG[index__]) && (obj__!=null)) \
          obj__.m_field_automation(null, what__, str__); \
    end \
  end

// M_OVM_FIELD_SET_QUEUE_OBJECT
// -----------------------------

`define M_OVM_FIELD_SET_QUEUE_OBJECT(ARG,FLAG) \
  `M_OVM_FIELD_SET_QUEUE_OBJECT_TYPE(ARG, FLAG) \
  if((what__ >= OVM_START_FUNCS && what__ <= OVM_END_FUNCS) && (((FLAG)&OVM_READONLY) == 0)) begin \
    ovm_object obj__; \
    for(int index__=0; index__<ARG.size(); ++index__) begin \
       if($cast(obj__,ARG[index__]) && (obj__!=null)) \
          obj__.m_field_automation(null, what__, str__); \
    end \
  end

`endif //OVM_EMPTY_MACROS

`endif  // OVM_OBJECT_DEFINES_SVH

