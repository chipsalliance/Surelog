// $Id: ovm_packer.svh,v 1.15 2010/03/12 20:52:36 jlrose Exp $
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

`ifndef OVM_PACKER_SVH
`define OVM_PACKER_SVH

//------------------------------------------------------------------------------
// CLASS: ovm_packer
//
// The ovm_packer class provides a policy object for packing and unpacking
// ovm_objects. The policies determine how packing and unpacking should be done.
// Packing an object causes the object to be placed into a bit (byte or int)
// array. If the `ovm_field_* macro are used to implement pack and unpack,
// by default no metadata information is stored for the packing of dynamic
// objects (strings, arrays, class objects).
//
//-------------------------------------------------------------------------------

// Maximum bytes for the packer array.
`ifndef OVM_PACKER_MAX_BYTES
  `define OVM_PACKER_MAX_BYTES OVM_STREAMBITS
`endif

typedef bit signed [(`OVM_PACKER_MAX_BYTES*8)-1:0] ovm_pack_bitstream_t;

class ovm_packer;

  //----------------//
  // Group: Packing //
  //----------------//
  
  // Function: pack_field
  //
  // Packs an integral value (less than or equal to 4096 bits) into the
  // packed array. ~size~ is the number of bits of ~value~ to pack.

  extern virtual function void pack_field (ovm_bitstream_t value, int size);


  // Function: pack_field_int
  //
  // Packs the integral value (less than or equal to 64 bits) into the
  // pack array.  The ~size~ is the number of bits to pack, usually obtained by
  // ~$bits~. This optimized version of <pack_field> is useful for sizes up
  // to 64 bits.

  extern virtual function void pack_field_int (logic[63:0] value, int size);


  // Function: pack_string
  //
  // Packs a string value into the pack array. 
  //
  // When the metadata flag is set, the packed string is terminated by a null
  // character to mark the end of the string.
  //
  // This is useful for mixed language communication where unpacking may occur
  // outside of SystemVerilog OVM.

  extern virtual function void pack_string (string value);


  // Function: pack_time
  //
  // Packs a time ~value~ as 64 bits into the pack array.

  extern virtual function void pack_time (time value); 


  // Function: pack_real
  //
  // Packs a real ~value~ as 64 bits into the pack array. 
  //
  // The real ~value~ is converted to a 6-bit scalar value using the function
  // $real2bits before it is packed into the array.

  extern virtual function void pack_real (real value);


  // Function: pack_object
  //
  // Packs an object value into the pack array. 
  //
  // A 4-bit header is inserted ahead of the string to indicate the number of
  // bits that was packed. If a null object was packed, then this header will
  // be 0. 
  //
  // This is useful for mixed-language communication where unpacking may occur
  // outside of SystemVerilog OVM.

  extern virtual function void pack_object (ovm_object value);


  //------------------//
  // Group: Unpacking //
  //------------------//
  
  // Function: is_null
  //
  // This method is used during unpack operations to peek at the next 4-bit
  // chunk of the pack data and determine if it is 0.
  //
  // If the next four bits are all 0, then the return value is a 1; otherwise
  // it is 0. 
  //
  // This is useful when unpacking objects, to decide whether a new object
  // needs to be allocated or not.

  extern virtual function bit is_null ();


  // Function: unpack_field_int
  //
  // Unpacks bits from the pack array and returns the bit-stream that was
  // unpacked. 
  //
  // ~size~ is the number of bits to unpack; the maximum is 64 bits. 
  // This is a more efficient variant than unpack_field when unpacking into
  // smaller vectors.

  extern virtual function logic[63:0] unpack_field_int (int size);


  // Function: unpack_field
  //
  // Unpacks bits from the pack array and returns the bit-stream that was
  // unpacked. ~size~ is the number of bits to unpack; the maximum is 4096 bits.

  extern virtual function ovm_bitstream_t unpack_field (int size);


  // Function: unpack_string
  //
  // Unpacks a string. 
  //
  // num_chars bytes are unpacked into a string. If num_chars is -1 then
  // unpacking stops on at the first null character that is encountered.

  extern virtual function string unpack_string (int num_chars=-1);


  // Function: unpack_time
  //
  // Unpacks the next 64 bits of the pack array and places them into a
  // time variable.

  extern virtual function time unpack_time (); 


  // Function: unpack_real
  //
  // Unpacks the next 64 bits of the pack array and places them into a
  // real variable. 
  //
  // The 64 bits of packed data are converted to a real using the $bits2real
  // system function.

  extern virtual function real unpack_real ();


  // Function: unpack_object
  //
  // Unpacks an object and stores the result into ~value~. 
  //
  // ~value~ must be an allocated object that has enough space for the data
  // being unpacked. The first four bits of packed data are used to determine
  // if a null object was packed into the array. 
  //
  // The <is_null> function can be used to peek at the next four bits in
  // the pack array before calling this method.

  extern virtual function void unpack_object (ovm_object value);


  // Function: get_packed_size
  //
  // Returns the number of bits that were packed.

  extern virtual function int get_packed_size(); 


  //------------------//
  // Group: Variables //
  //------------------//

  // Variable: physical
  //
  // This bit provides a filtering mechanism for fields.
  //
  // The <abstract> and physical settings allow an object to distinguish between
  // two different classes of fields. It is up to you, in the
  // <ovm_object::do_pack> and <ovm_object::do_unpack> methods, to test the
  // setting of this field if you want to use it as a filter.

  bit physical = 1;


  // Variable: abstract
  //
  // This bit provides a filtering mechanism for fields. 
  //
  // The abstract and physical settings allow an object to distinguish between
  // two different classes of fields. It is up to you, in the
  // <ovm_object::do_pack> and <ovm_object::do_unpack> routines, to test the
  // setting of this field if you want to use it as a filter.

  bit abstract = 0;


  // Variable: use_metadata
  //
  // This flag indicates whether to encode metadata when packing dynamic data,
  // or to decode metadata when unpacking.  Implementations of <do_pack> and
  // <do_unpack> should regard this bit when performing their respective
  // operation. When set, metadata should be encoded as follows:
  //
  // - For strings, pack an additional null byte after the string is packed.
  //
  // - For objects, pack 4 bits prior to packing the object itself. Use 4'b0000
  //   to indicate the object being packed is null, otherwise pack 4'b0001 (the
  //   remaining 3 bits are reserved).
  //
  // - For queues, dynamic arrays, and associative arrays, pack 32 bits
  //   indicating the size of the array prior to to packing individual elements.

  bit use_metadata = 0;


  // Variable: big_endian
  //
  // This bit determines the order that integral data is packed (using
  // <pack_field>, <pack_field_int>, <pack_time>, or <pack_real>) and how the
  // data is unpacked from the pack array (using <unpack_field>,
  // <unpack_field_int>, <unpack_time>, or <unpack_real>). When the bit is set,
  // data is associated msb to lsb; otherwise, it is associated lsb to msb. 
  //
  // The following code illustrates how data can be associated msb to lsb and
  // lsb to msb:
  //
  //|  class mydata extends ovm_object;
  //|
  //|    logic[15:0] value = 'h1234;
  //|
  //|    function void do_pack (ovm_packer packer);
  //|      packer.pack_field_int(value, 16);
  //|    endfunction
  //|
  //|    function void do_unpack (ovm_packer packer);
  //|      value = packer.unpack_field_int(16);
  //|    endfunction
  //|  endclass
  //|
  //|  mydata d = new;
  //|  bit bits[];
  //|
  //|  initial begin
  //|    d.pack(bits);  // 'b0001001000110100
  //|    ovm_default_packer.big_endian = 0;
  //|    d.pack(bits);  // 'b0010110001001000
  //|  end

  bit big_endian = 1;


  // variables and methods primarily for internal use

  static bit bitstream[];   // local bits for (un)pack_bytes
  static bit fabitstream[]; // field automation bits for (un)pack_bytes
  int count = 0;            // used to count the number of packed bits
  ovm_scope_stack scope= new;

  bit   reverse_order = 0;  //flip the bit order around
  byte  byte_size     = 8;  //set up bytesize for endianess
  int   word_size     = 16; //set up worksize for endianess
  bit   nopack        = 0;  //only count packable bits

  ovm_recursion_policy_enum policy = OVM_DEFAULT_POLICY;

  ovm_pack_bitstream_t m_bits = 0;
  int m_packed_size  = 0;

  extern virtual function void unpack_object_ext  (inout ovm_object value);

  extern virtual function ovm_pack_bitstream_t get_packed_bits ();

  extern virtual function bit  unsigned get_bit  (int unsigned index);
  extern virtual function byte unsigned get_byte (int unsigned index);
  extern virtual function int  unsigned get_int  (int unsigned index);

  extern virtual function void get_bits (ref bit unsigned bits[]);
  extern virtual function void get_bytes(ref byte unsigned bytes[]);
  extern virtual function void get_ints (ref int unsigned ints[]);

  extern virtual function void put_bits (ref bit unsigned bitstream[]);
  extern virtual function void put_bytes(ref byte unsigned bytestream[]);
  extern virtual function void put_ints (ref int unsigned intstream[]);

  extern virtual function void set_packed_size(); 
  extern function void index_error(int index, string id, int sz);
  extern function bit enough_bits(int needed, string id);

  extern function void reset();

endclass

`endif // OVM_PACKER_SVH
