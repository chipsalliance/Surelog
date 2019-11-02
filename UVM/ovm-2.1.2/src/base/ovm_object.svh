// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_object.svh#33 $
//-----------------------------------------------------------------------------
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
//-----------------------------------------------------------------------------


`ifndef OVM_OBJECT_SVH
`define OVM_OBJECT_SVH

/*
typedef class ovm_printer;
typedef class ovm_table_printer;
typedef class ovm_tree_printer;
typedef class ovm_line_printer;
typedef class ovm_comparer;
typedef class ovm_packer;
typedef class ovm_recorder;
*/
typedef class ovm_report_object;
typedef class ovm_object_wrapper;
typedef class ovm_objection;

// internal
//typedef class ovm_copy_map;
typedef class ovm_status_container;

//------------------------------------------------------------------------------
//
// CLASS: ovm_object
//
// The ovm_object class is the base class for all OVM data and hierarchical 
// classes. Its primary role is to define a set of methods for such common
// operations as <create>, <copy>, <compare>, <print>, and <record>. Classes
// deriving from ovm_object must implement the pure virtual methods such as 
// <create> and <get_type_name>.
//
//------------------------------------------------------------------------------

virtual class ovm_object extends ovm_void;


  // Function: new
  //
  // Creates a new ovm_object with the given instance ~name~. If ~name~ is not
  // supplied, the object is unnamed.

  extern function new (string name="");


  // Group: Seeding

  // Variable: use_ovm_seeding
  //
  // This bit enables or disables the OVM seeding mechanism. It globally affects
  // the operation of the reseed method. 
  //
  // When enabled, OVM-based objects are seeded based on their type and full
  // hierarchical name rather than allocation order. This improves random
  // stability for objects whose instance names are unique across each type.
  // The <ovm_component> class is an example of a type that has a unique
  // instance name.

  static bit use_ovm_seeding = 1;


  // Function: reseed
  //
  // Calls ~srandom~ on the object to reseed the object using the OVM seeding
  // mechanism, which sets the seed based on type name and instance name instead
  // of based on instance position in a thread. 
  //
  // If the <use_ovm_seeding> static variable is set to 0, then reseed() does
  // not perform any function. 

  extern function void reseed ();


  // Group: Identification

  // Function: set_name
  //
  // Sets the instance name of this object, overwriting any previously
  // given name.

  extern virtual function void set_name (string name);


  // Function: get_name
  //
  // Returns the name of the object, as provided by the ~name~ argument in the
  // <new> constructor or <set_name> method.

  extern virtual function string get_name ();


  // Function: get_full_name
  //
  // Returns the full hierarchical name of this object. The default
  // implementation is the same as <get_name>, as ovm_objects do not inherently
  // possess hierarchy. 
  //
  // Objects possessing hierarchy, such as <ovm_components>, override the default
  // implementation. Other objects might be associated with component hierarchy
  // but are not themselves components. For example, <ovm_sequence #(REQ,RSP)>
  // classes are typically associated with a <ovm_sequencer #(REQ,RSP)>. In this
  // case, it is useful to override get_full_name to return the sequencer's
  // full name concatenated with the sequence's name. This provides the sequence
  // a full context, which is useful when debugging.

  extern virtual function string get_full_name ();


  // Function: get_inst_id
  //
  // Returns the object's unique, numeric instance identifier.

  extern virtual function int get_inst_id ();


  // Function: get_inst_count
  //
  // Returns the current value of the instance counter, which represents the
  // total number of ovm_object-based objects that have been allocated in
  // simulation. The instance counter is used to form a unique numeric instance
  // identifier.

  extern static  function int get_inst_count();


  // Function: get_type
  //
  // Returns the type-proxy (wrapper) for this object. The <ovm_factory>'s
  // type-based override and creation methods take arguments of
  // <ovm_object_wrapper>. This method, if implemented, can be used as convenient
  // means of supplying those arguments.
  //
  // The default implementation of this method produces an error and returns
  // null. To enable use of this method, a user's subtype must implement a
  // version that returns the subtype's wrapper.
  //
  // For example:
  //
  //|  class cmd extends ovm_object;
  //|    typedef ovm_object_registry #(cmd) type_id;
  //|    static function type_id get_type();
  //|      return type_id::get();
  //|    endfunction
  //|  endclass
  //
  // Then, to use:
  //
  //|  factory.set_type_override(cmd::get_type(),subcmd::get_type());
  //
  // This function is implemented by the `ovm_*_utils macros, if employed.

  extern static function ovm_object_wrapper get_type ();


  // Function: get_object_type
  //
  // Returns the type-proxy (wrapper) for this object. The <ovm_factory>'s
  // type-based override and creation methods take arguments of
  // <ovm_object_wrapper>. This method, if implemented, can be used as convenient
  // means of supplying those arguments. This method is the same as the static
  // <get_type> method, but uses an already allocated object to determine
  // the type-proxy to access (instead of using the static object.
  //
  // The default implementation of this method does a factory lookup of the
  // proxy using the return value from <get_type_name>. If the type returned
  // by <get_type_name> is not registered with the factory, then a null 
  // handle is returned.
  //
  // For example:
  //
  //|  class cmd extends ovm_object;
  //|    typedef ovm_object_registry #(cmd) type_id;
  //|    static function type_id get_type();
  //|      return type_id::get();
  //|    endfunction
  //|    virtual function type_id get_object_type();
  //|      return type_id::get();
  //|    endfunction
  //|  endclass
  //
  // This function is implemented by the `ovm_*_utils macros, if employed.

  extern virtual function ovm_object_wrapper get_object_type ();


  // Function: get_type_name
  //
  // This function returns the type name of the object, which is typically the
  // type identifier enclosed in quotes. It is used for various debugging
  // functions in the library, and it is used by the factory for creating
  // objects.
  //
  // This function must be defined in every derived class. 
  //
  // A typical implementation is as follows:
  //
  //|  class mytype extends ovm_object;
  //|    ...
  //|    const static string type_name = "mytype";
  //|
  //|    virtual function string get_type_name();
  //|      return type_name;
  //|    endfunction
  //
  // We define the <type_name> static variable to enable access to the type name
  // without need of an object of the class, i.e., to enable access via the
  // scope operator, ~mytype::type_name~.

  virtual function string get_type_name (); return "<unknown>"; endfunction


  // Group: Creation

  // Function: create
  //
  // The create method allocates a new object of the same type as this object
  // and returns it via a base ovm_object handle. Every class deriving from
  // ovm_object, directly or indirectly, must implement the create method.
  //
  // A typical implementation is as follows:
  //
  //|  class mytype extends ovm_object;
  //|    ...
  //|    virtual function ovm_object create(string name="");
  //|      mytype t = new(name);
  //|      return t;
  //|    endfunction 

  virtual function ovm_object create (string name=""); return null; endfunction

  
  // Function: clone
  //
  // The clone method creates and returns an exact copy of this object.
  // 
  // The default implementation calls <create> followed by <copy>. As clone is
  // virtual, derived classes may override this implementation if desired. 

  extern virtual function ovm_object clone ();


  // Group: Printing

  // Function: print
  // 
  // The print method deep-prints this object's properties in a format and
  // manner governed by the given ~printer~ argument; if the ~printer~ argument
  // is not provided, the global <ovm_default_printer> is used. See 
  // <ovm_printer> for more information on printer output formatting. See also
  // <ovm_line_printer>, <ovm_tree_printer>, and <ovm_table_printer> for details
  // on the pre-defined printer "policies," or formatters, provided by the OVM.
  //
  // The ~print~ method is not virtual and must not be overloaded. To include
  // custom information in the ~print~ and ~sprint~ operations, derived classes
  // must override the <do_print> method and use the provided printer policy
  // class to format the output.

  extern function void print (ovm_printer printer=null);


  // Function: sprint
  //
  // The ~sprint~ method works just like the <print> method, except the output
  // is returned in a string rather than displayed. 
  //
  // The ~sprint~ method is not virtual and must not be overloaded. To include
  // additional fields in the ~print~ and ~sprint~ operation, derived classes
  // must override the <do_print> method and use the provided printer policy
  // class to format the output. The printer policy will manage all string
  // concatenations and provide the string to ~sprint~ to return to the caller.

  extern function string sprint (ovm_printer printer=null); 


  // Function: do_print
  //
  // The ~do_print~ method is the user-definable hook called by <print> and
  // <sprint> that allows users to customize what gets printed or sprinted 
  // beyond the field information provided by the <`ovm_field_*> macros.
  //
  // The ~printer~ argument is the policy object that governs the format and
  // content of the output. To ensure correct <print> and <sprint> operation,
  // and to ensure a consistent output format, the ~printer~ must be used
  // by all <do_print> implementations. That is, instead of using $display or
  // string concatenations directly, a ~do_print~ implementation must call
  // through the ~printer's~ API to add information to be printed or sprinted.
  //
  // An example implementation of ~do_print~ is as follows:
  //
  //| class mytype extends ovm_object;
  //|   data_obj data;
  //|   int f1;
  //|   virtual function void do_print (ovm_printer printer);
  //|     super.do_print(printer);
  //|     printer.print_field("f1", f1, $bits(f1), DEC);
  //|     printer.print_object("data", data);
  //|   endfunction
  //
  // Then, to print and sprint the object, you could write:
  //
  //| mytype t = new;
  //| t.print();
  //| ovm_report_info("Received",t.sprint());
  //
  // See <ovm_printer> for information about the printer API.

  extern virtual function void do_print (ovm_printer printer);


  // Function: convert2string
  //
  // This virtual function is a user-definable hook, called directly by the
  // user, that allows users to provide object information in the form of
  // a string. Unlike <sprint>, there is no requirement to use an <ovm_printer>
  // policy object. As such, the format and content of the output is fully
  // customizable, which may be suitable for applications not requiring the
  // consistent formatting offered by the <print>/<sprint>/<do_print>
  // API.
  //
  // Note: Fields declared in <`ovm_field_*> macros, if used, will not
  // automatically appear in calls to convert2string.
  //
  // An example implementation of convert2string follows.
  // 
  //| class base extends ovm_object;
  //|   string field = "foo";
  //|   virtual function string convert2string();
  //|     convert2string = {"base_field=",field};
  //|   endfunction
  //| endclass
  //| 
  //| class obj2 extends ovm_object;
  //|   string field = "bar";
  //|   virtual function string convert2string();
  //|     convert2string = {"child_field=",field};
  //|   endfunction
  //| endclass
  //| 
  //| class obj extends base;
  //|   int addr = 'h123;
  //|   int data = 'h456;
  //|   bit write = 1;
  //|   obj2 child = new;
  //|   virtual function string convert2string();
  //|      convert2string = {super.convert2string(),
  //|        $psprintf(" write=%0d addr=%8h data=%8h ",write,addr,data),
  //|        child.convert2string()};
  //|   endfunction
  //| endclass
  //
  // Then, to display an object, you could write:
  //
  //| obj o = new;
  //| ovm_report_info("BusMaster",{"Sending:\n ",o.convert2string()});
  //
  // The output will look similar to:
  //
  //| OVM_INFO @ 0: reporter [BusMaster] Sending:
  //|    base_field=foo write=1 addr=00000123 data=00000456 child_field=bar


  extern virtual function string convert2string;


  // Group: Recording

  // Function: record
  //
  // The record method deep-records this object's properties according to an
  // optional ~recorder~ policy. The method is not virtual and must not be
  // overloaded. To include additional fields in the record operation, derived
  // classes should override the <do_record> method.
  //
  // The optional ~recorder~ argument specifies the recording policy, which
  // governs how recording takes place. If a recorder policy is not provided
  // explicitly, then the global <ovm_default_recorder> policy is used. See
  // ovm_recorder for information.
  //
  // A simulator's recording mechanism is vendor-specific. By providing access
  // via a common interface, the ovm_recorder policy provides vendor-independent
  // access to a simulator's recording capabilities.

  extern function void record (ovm_recorder recorder=null);


  // Function: do_record
  //
  // The do_record method is the user-definable hook called by the <record>
  // method. A derived class should override this method to include its fields
  // in a record operation.
  //
  // The ~recorder~ argument is policy object for recording this object. A
  // do_record implementation should call the appropriate recorder methods for
  // each of its fields. Vendor-specific recording implementations are
  // encapsulated in the ~recorder~ policy, thereby insulating user-code from
  // vendor-specific behavior. See <ovm_recorder> for more information.
  //
  // A typical implementation is as follows:
  //
  //| class mytype extends ovm_object;
  //|   data_obj data;
  //|   int f1;
  //|   function void do_record (ovm_recorder recorder);
  //|     recorder.record_field_int("f1", f1, $bits(f1), DEC);
  //|     recorder.record_object("data", data);
  //|   endfunction

  extern virtual function void do_record (ovm_recorder recorder);


  // Group: Copying

  // Function: copy
  //
  // The copy method returns a deep copy of this object.
  //
  // The copy method is not virtual and should not be overloaded in derived
  // classes. To copy the fields of a derived class, that class should override
  // the <do_copy> method.

  extern function void copy (ovm_object rhs);


  // Function: do_copy
  //
  // The do_copy method is the user-definable hook called by the copy method.
  // A derived class should override this method to include its fields in a copy
  // operation.
  //
  // A typical implementation is as follows:
  //
  //|  class mytype extends ovm_object;
  //|    ...
  //|    int f1;
  //|    function void do_copy (ovm_object rhs);
  //|      mytype rhs_;
  //|      super.do_copy(rhs);
  //|      $cast(rhs_,rhs);
  //|      field_1 = rhs_.field_1;
  //|    endfunction
  //
  // The implementation must call ~super.do_copy~, and it must $cast the rhs
  // argument to the derived type before copying. 

  extern virtual function void do_copy (ovm_object rhs);


  // Group: Comparing

  // Function: compare
  //
  // The compare method deep compares this data object with the object provided
  // in the ~rhs~ (right-hand side) argument.
  //
  // The compare method is not virtual and should not be overloaded in derived
  // classes. To compare the fields of a derived class, that class should
  // override the <do_compare> method.
  //
  // The optional ~comparer~ argument specifies the comparison policy. It allows
  // you to control some aspects of the comparison operation. It also stores the
  // results of the comparison, such as field-by-field miscompare information
  // and the total number of miscompares. If a compare policy is not provided,
  // then the global ~ovm_default_comparer~ policy is used. See <ovm_comparer> 
  // for more information.

  extern function bit compare (ovm_object rhs, ovm_comparer comparer=null);


  // Function: do_compare
  //
  // The do_compare method is the user-definable hook called by the <compare>
  // method. A derived class should override this method to include its fields
  // in a compare operation.
  //
  // A typical implementation is as follows:
  //
  //|  class mytype extends ovm_object;
  //|    ...
  //|    int f1;
  //|    virtual function bit do_compare (ovm_object rhs,ovm_comparer comparer);
  //|      mytype rhs_;
  //|      do_compare = super.do_compare(rhs,comparer);
  //|      $cast(rhs_,rhs);
  //|      do_compare &= comparer.compare_field_int("f1", f1, rhs_.f1);
  //|    endfunction
  //
  // A derived class implementation must call super.do_compare to ensure its
  // base class' properties, if any, are included in the comparison. Also, the
  // rhs argument is provided as a generic ovm_object. Thus, you must $cast it
  // to the type of this object before comparing. 
  //
  // The actual comparison should be implemented using the ovm_comparer object
  // rather than direct field-by-field comparison. This enables users of your
  // class to customize how comparisons are performed and how much miscompare
  // information is collected. See ovm_comparer for more details.

  extern virtual function bit do_compare (ovm_object  rhs,
                                          ovm_comparer comparer);

  // Group: Packing

  // Function: pack

  extern function int pack (ref bit bitstream[],
                            input ovm_packer packer=null);

  // Function: pack_bytes

  extern function int pack_bytes (ref byte unsigned bytestream[],
                                  input ovm_packer packer=null);

  // Function: pack_ints
  //
  // The pack methods bitwise-concatenate this object's properties into an array
  // of bits, bytes, or ints. The methods are not virtual and must not be
  // overloaded. To include additional fields in the pack operation, derived
  // classes should override the <do_pack> method.
  //
  // The optional ~packer~ argument specifies the packing policy, which governs
  // the packing operation. If a packer policy is not provided, the global
  // <ovm_default_packer> policy is used. See <ovm_packer> for more information.
  //
  // The return value is the total number of bits packed into the given array.
  // Use the array's built-in ~size~ method to get the number of bytes or ints
  // consumed during the packing process.

  extern function int pack_ints (ref int unsigned intstream[],
                                 input ovm_packer packer=null);
  
  
  // Function: do_pack
  //
  // The do_pack method is the user-definable hook called by the <pack> methods.
  // A derived class should override this method to include its fields in a pack
  // operation.
  //
  // The ~packer~ argument is the policy object for packing. The policy object
  // should be used to pack objects. 
  //
  // A typical example of an object packing itself is as follows
  //
  //|  class mysubtype extends mysupertype;
  //|    ...
  //|    shortint myshort;
  //|    obj_type myobj;
  //|    byte myarray[];
  //|    ...
  //|    function void do_pack (ovm_packer packer);
  //|      super.do_pack(packer); // pack mysupertype properties
  //|      packer.pack_field_int(myarray.size(), 32);
  //|      foreach (myarray)
  //|        packer.pack_field_int(myarray[index], 8);
  //|      packer.pack_field_int(myshort, $bits(myshort));
  //|      packer.pack_object(myobj);
  //|    endfunction
  //
  // The implementation must call ~super.do_pack~ so that base class properties
  // are packed as well.
  //
  // If your object contains dynamic data (object, string, queue, dynamic array,
  // or associative array), and you intend to unpack into an equivalent data
  // structure when unpacking, you must include meta-information about the
  // dynamic data when packing as follows.
  //
  //  - For queues, dynamic arrays, or associative arrays, pack the number of
  //    elements in the array in the 32 bits immediately before packing
  //    individual elements, as shown above.
  //
  //  - For string data types, append a zero byte after packing the string
  //    contents.
  //
  //  - For objects, pack 4 bits immediately before packing the object. For null
  //    objects, pack 4'b0000. For non-null objects, pack 4'b0001.
  //
  // When the `ovm_*_field macros are used, the above meta information is
  // included provided the <ovm_packer>'s <use_metadata> variable is set.
  //
  // Packing order does not need to match declaration order. However, unpacking
  // order must match packing order.

  extern virtual function void do_pack (ovm_packer packer);


  // Group: Unpacking

  // Function: unpack

  extern function int unpack (ref   bit        bitstream[],
                              input ovm_packer packer=null);

  // Function: unpack_bytes

  extern function int unpack_bytes (ref byte unsigned bytestream[],
                                    input ovm_packer packer=null);
  
  // Function: unpack_ints
  //
  // The unpack methods extract property values from an array of bits, bytes, or
  // ints. The method of unpacking _must_ exactly correspond to the method of
  // packing. This is assured if (a) the same ~packer~ policy is used to pack
  // and unpack, and (b) the order of unpacking is the same as the order of
  // packing used to create the input array.
  //
  // The unpack methods are fixed (non-virtual) entry points that are directly
  // callable by the user. To include additional fields in the <unpack>
  // operation, derived classes should override the <do_unpack> method.
  //
  // The optional ~packer~ argument specifies the packing policy, which governs
  // both the pack and unpack operation. If a packer policy is not provided,
  // then the global ~ovm_default_packer~ policy is used. See ovm_packer for
  // more information.
  //
  // The return value is the actual number of bits unpacked from the given array.
  
  extern function int unpack_ints (ref   int unsigned intstream[],
                                   input ovm_packer packer=null);


  // Function: do_unpack
  //
  // The do_unpack method is the user-definable hook called by the <unpack>
  // method. A derived class should override this method to include its fields
  // in an unpack operation.
  //
  // The ~packer~ argument is the policy object for both packing and unpacking.
  // It must be the same packer used to pack the object into bits. Also,
  // do_unpack must unpack fields in the same order in which they were packed.
  // See <ovm_packer> for more information.
  //
  // The following implementation corresponds to the example given in do_pack.
  //
  //|  function void do_unpack (ovm_packer packer);
  //|   int sz;
  //|    super.do_unpack(packer); // unpack super's properties
  //|    sz = packer.unpack_field_int(myarray.size(), 32);
  //|    myarray.delete();
  //|    for(int index=0; index<sz; index++)
  //|      myarray[index] = packer.unpack_field_int(8);
  //|    myshort = packer.unpack_field_int($bits(myshort));
  //|    packer.unpack_object(myobj);
  //|  endfunction
  //
  // If your object contains dynamic data (object, string, queue, dynamic array,
  // or associative array), and you intend to <unpack> into an equivalent data
  // structure, you must have included meta-information about the dynamic data
  // when it was packed. 
  //
  // - For queues, dynamic arrays, or associative arrays, unpack the number of
  //   elements in the array from the 32 bits immediately before unpacking
  //   individual elements, as shown above.
  //
  // - For string data types, unpack into the new string until a null byte is
  //   encountered.
  //
  // - For objects, unpack 4 bits into a byte or int variable. If the value
  //   is 0, the target object should be set to null and unpacking continues to
  //   the next property, if any. If the least significant bit is 1, then the
  //   target object should be allocated and its properties unpacked.

  extern virtual function void do_unpack (ovm_packer packer);


  // Group: Configuration

  // Function: set_int_local

  extern virtual function void  set_int_local    (string      field_name,
                                                  ovm_bitstream_t value,
                                                  bit         recurse=1);

  // Function: set_string_local

  extern virtual function void  set_string_local (string field_name,
                                                  string value,
                                                  bit    recurse=1);

  // Function: set_object_local
  //
  // These methods provide write access to integral, string, and 
  // ovm_object-based properties indexed by a ~field_name~ string. The object
  // designer choose which, if any, properties will be accessible, and overrides
  // the appropriate methods depending on the properties' types. For objects,
  // the optional ~clone~ argument specifies whether to clone the ~value~
  // argument before assignment.
  //
  // The global <ovm_is_match> function is used to match the field names, so
  // ~field_name~ may contain wildcards.
  //
  // An example implementation of all three methods is as follows.
  //
  //| class mytype extends ovm_object;
  //|
  //|   local int myint;
  //|   local byte mybyte;
  //|   local shortint myshort; // no access
  //|   local string mystring;
  //|   local obj_type myobj;
  //| 
  //|   // provide access to integral properties
  //|   function void set_int_local(string field_name, ovm_bitstream_t value);
  //|     if (ovm_is_match (field_name, "myint"))
  //|       myint = value;
  //|     else if (ovm_is_match (field_name, "mybyte"))
  //|       mybyte = value;
  //|   endfunction
  //| 
  //|   // provide access to string properties
  //|   function void set_string_local(string field_name, string value);
  //|     if (ovm_is_match (field_name, "mystring"))
  //|       mystring = value;
  //|   endfunction
  //| 
  //|   // provide access to sub-objects
  //|   function void set_object_local(string field_name, ovm_object value,
  //|                                  bit clone=1);
  //|     if (ovm_is_match (field_name, "myobj")) begin
  //|       if (value != null) begin
  //|         obj_type tmp;
  //|         // if provided value is not correct type, produce error
  //|         if (!$cast(tmp, value) 
  //|           /* error */
  //|         else
  //|           myobj = clone ? tmp.clone() : tmp;
  //|       end
  //|       else
  //|         myobj = null; // value is null, so simply assign null to myobj
  //|     end
  //|   endfunction
  //|   ...
  //
  // Although the object designer implements these methods to provide outside
  // access to one or more properties, they are intended for internal use (e.g.,
  // for command-line debugging and auto-configuration) and should not be called
  // directly by the user.

  extern virtual function void  set_object_local (string      field_name,
                                                  ovm_object  value,
                                                  bit         clone=1,
                                                  bit         recurse=1);



  //---------------------------------------------------------------------------
  //                 **** Internal Methods and Properties ***
  //                           Do not use directly
  //---------------------------------------------------------------------------

  extern local function void m_pack        (inout ovm_packer packer);
  extern local function void m_unpack_pre  (inout ovm_packer packer);
  extern local function void m_unpack_post (ovm_packer packer);

  // The print_matches bit causes an informative message to be printed
  // when a field is set using one of the set methods.

  local string m_leaf_name;

  static bit print_matches = 0;

  extern static function void print_field_match (string fnc, string match);

  extern virtual function void m_field_automation (ovm_object  tmp_data__,  
                                                   int what__, 
                                                   string str__);
  extern protected function int m_do_data (string arg,
                                           inout ovm_bitstream_t lhs,
                                           input ovm_bitstream_t rhs,
                                           int what, int bits, int flag);
  extern protected function int m_do_data_real (string arg,
                                                inout real lhs,
                                                input real rhs,
                                                int what, int flag);
  extern protected function int m_do_data_object (string arg,
                                                  inout ovm_object  lhs,
                                                  input ovm_object  rhs,
                                                  int what, int flag);
  extern protected function int m_do_data_string (string arg,
                                                  inout string lhs,
                                                  input string rhs,
                                                  int what, int flag);
  extern protected function void m_record_field_object (string arg,
                                          ovm_object value,
                                          ovm_recorder recorder=null,
                                          int flag=OVM_DEFAULT);
  extern protected function int m_do_set (string match, string arg,
                                          inout ovm_bitstream_t  lhs, 
                                          input int what, int flag);
  extern protected function int m_do_set_string (string match,
                                                 string arg, inout string lhs,
                                                 input int what, int flag);
  extern protected function int m_do_set_object (string match,
                                                 string arg,
                                                 inout ovm_object lhsobj, 
                                                 input int what, int flag);

  extern protected function string  m_get_function_type  (int what);

  static protected int m_inst_count = 0;
  local int m_inst_id;

  extern protected virtual function ovm_report_object m_get_report_object();

  extern static function ovm_status_container init_status();

  static protected ovm_status_container m_sc = init_status();

  static function ovm_status_container m_get_status(); return m_sc; endfunction

  // The following members are used for verifying the integrity of the 
  // optional ovm_field macros.
  static protected int m_field_array[string];
  extern protected function void m_do_field_check(string field);
  extern static protected function void m_delete_field_array();

  // deprecated - do not use
  extern virtual function string do_sprint (ovm_printer printer); 

endclass


//------------------------------------------------------------------------------
//
// CLASS- ovm_status_container
//
// Internal class to contain status information for automation methods.
//
// This container class needs to be defined ahead of the ovm_object class
// which uses it to work around a bug in ius 6.11 regarding class in packages.
// This class is just for internal usage. It is a class instead of a struct
// becauses structs currently cannot hold class object handles.
//
//------------------------------------------------------------------------------

class ovm_status_container;
  //Since there is a cost to saving the field string, only do so if needed.
  static bit          save_last_field = 0;
  static string       last_field     = "";

  static bit          warning    = 0;
  static bit          status     = 0;
  static ovm_bitstream_t  bitstream  = 0;
  static int          intv       = 0;
  static int          element    = 0;
  static string       stringv    = "";
  static string       scratch1   = "";
  static string       scratch2   = "";
  static string       key        = "";
  static ovm_object   object     = null;
  static bit          array_warning_done = 0;
  static ovm_scope_stack scope       = init_scope();  //For get-set operations

  extern static function string get_full_scope_arg ();
  extern static function ovm_scope_stack init_scope();
endclass

//------------------------------------------------------------------------------
//
// CLASS- ovm_copy_map
//
//
// Internal class used to map rhs to lhs so when a cycle is found in the rhs,
// the correct lhs object can be bound to it.
//------------------------------------------------------------------------------

class ovm_copy_map;
  local ovm_object m_map[ovm_object];
  function void set(ovm_object key, ovm_object obj);
    m_map[key] = obj;
  endfunction
  function ovm_object get(ovm_object key);
    if (m_map.exists(key))
       return m_map[key];
    return null;
  endfunction
  function void clear();
    m_map.delete();
  endfunction 
  function void delete(ovm_object v);
    m_map.delete(v);
  endfunction 
endclass


//------------------------------------------------------------------------------
//
// CLASS- ovm_options_container
//
// Internal class.
//------------------------------------------------------------------------------

class ovm_options_container;
  ovm_comparer    comparer;
  ovm_packer      packer;
  ovm_recorder    recorder;
  ovm_printer     printer;
  bit             clone = 1;
  extern function new();
  extern static function ovm_options_container init();
endclass


`endif // OVM_OBJECT_SVH
