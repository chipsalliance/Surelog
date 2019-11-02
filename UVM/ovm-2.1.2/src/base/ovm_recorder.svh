// $Id: ovm_recorder.svh,v 1.2 2009/12/14 22:39:41 jlrose Exp $
//-----------------------------------------------------------------------------
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
//-----------------------------------------------------------------------------

//------------------------------------------------------------------------------
//
// CLASS: ovm_recorder
//
// The ovm_recorder class provides a policy object for recording <ovm_objects>.
// The policies determine how recording should be done. 
//
// A default recorder instance, <ovm_default_recorder>, is used when the
// <ovm_object::record> is called without specifying a recorder.
//
//------------------------------------------------------------------------------

class ovm_recorder;

  int recording_depth = 0; 


  // Variable: tr_handle
  //
  // This is an integral handle to a transaction object. Its use is vendor
  // specific. 
  //
  // A handle of 0 indicates there is no active transaction object. 

  integer tr_handle = 0;


  // Variable: default_radix
  //
  // This is the default radix setting if <record_field> is called without
  // a radix.

  ovm_radix_enum default_radix = OVM_HEX;


  // Variable: physical
  //
  // This bit provides a filtering mechanism for fields. 
  //
  // The <abstract> and physical settings allow an object to distinguish between
  // two different classes of fields. 
  //
  // It is up to you, in the <ovm_object::do_record> method, to test the
  // setting of this field if you want to use the physical trait as a filter.

  bit physical = 1;


  // Variable: abstract
  //
  // This bit provides a filtering mechanism for fields. 
  //
  // The abstract and physical settings allow an object to distinguish between
  // two different classes of fields. 
  //
  // It is up to you, in the <ovm_object::do_record> method, to test the
  // setting of this field if you want to use the abstract trait as a filter.

  bit abstract = 1;


  // Variable: identifier
  //
  // This bit is used to specify whether or not an object's reference should be
  // recorded when the object is recorded. 

  bit identifier = 1;


  // Variable: recursion_policy
  //
  // Sets the recursion policy for recording objects. 
  //
  // The default policy is deep (which means to recurse an object).

  ovm_recursion_policy_enum policy = OVM_DEFAULT_POLICY;


  // Function: record_field
  //
  // Records an integral field (less than or equal to 4096 bits). ~name~ is the
  // name of the field. 
  //
  // ~value~ is the value of the field to record. ~size~ is the number of bits
  // of the field which apply. ~radix~ is the <ovm_radix_enum> to use.

  virtual function void record_field (string name, 
                                      ovm_bitstream_t value, 
                                      int size, 
                                      ovm_radix_enum  radix=OVM_NORADIX);
    if(tr_handle==0) return;
    scope.set_arg(name);

    if(!radix)
      radix = default_radix;

    case(radix)
      OVM_BIN:     ovm_set_attribute_by_name(tr_handle, scope.get_arg(), value, "'b",size);
      OVM_OCT:     ovm_set_attribute_by_name(tr_handle, scope.get_arg(), value, "'o",size);
      OVM_DEC:     ovm_set_attribute_by_name(tr_handle, scope.get_arg(), value, "'s",size);
      OVM_TIME:    ovm_set_attribute_by_name(tr_handle, scope.get_arg(), value, "'u",size);
      OVM_STRING:  ovm_set_attribute_by_name(tr_handle, scope.get_arg(), value, "'a",size);
      default: ovm_set_attribute_by_name(tr_handle, scope.get_arg(), value, "'x",size);
    endcase
  endfunction


  // Function: record_field_real
  //
  // Records an real field. ~value~ is the value of the field to record. 

  virtual function void record_field_real (string name, 
                                           real value);
    if(tr_handle==0) return;
    scope.set_arg(name);
    ovm_set_attribute_by_name(tr_handle, scope.get_arg(), value, "'r");
  endfunction


  // Function: record_object
  //
  // Records an object field. ~name~ is the name of the recorded field. 
  //
  // This method uses the recursion <policy> to determine whether or not to
  // recurse into the object.

  virtual function void record_object (string name, ovm_object value);
     int v;
    string str; 

    if(scope.in_hierarchy(value)) return;

    if(identifier) begin 
      `ifdef INCA
        $swrite(str, "%0d", value);
      `else
        str = "";
      `endif
      v = str.atoi(); 
      scope.set_arg(name);
      ovm_set_attribute_by_name(tr_handle, scope.get_arg(), v, "'s");
    end
  
    if(policy != OVM_REFERENCE) begin
      if(value!=null) begin
        scope.down(name, value);
        value.record(this);
        scope.up(value);
      end
    end

  endfunction


  // Function: record_string
  //
  // Records a string field. ~name~ is the name of the recorded field.
  
  virtual function void record_string (string name, string value);
    scope.set_arg(name);
    ovm_set_attribute_by_name(tr_handle, scope.get_arg(), ovm_string_to_bits(value), "'a");
  endfunction


  // Function: record_time
  //
  // Records a time value. ~name~ is the name to record to the database.
  
  
  virtual function void record_time (string name, time value); 
    record_field(name, value, 64, OVM_TIME); 
  endfunction


  // Function: record_generic
  //
  // Records the name-value pair, where value has been converted
  // to a string, e.g. via $psprintf("%<format>",<some variable>);
  
  virtual function void record_generic (string name, string value);
    record_string(name, value);
  endfunction


  ovm_scope_stack scope = new;

endclass



