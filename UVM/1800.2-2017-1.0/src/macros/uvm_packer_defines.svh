//----------------------------------------------------------------------
// Copyright 2018 Qualcomm, Inc.
// Copyright 2018 Cadence Design Systems, Inc.
// Copyright 2018 NVIDIA Corporation
// Copyright 2018 Cisco Systems, Inc.
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

`ifndef UVM_PACKER_DEFINES_SVH
 `define UVM_PACKER_DEFINES_SVH

//------------------------------------------------------------------------------
//
// MACROS for uvm_packer usage
//
// Provides a set of packing/unpacking macros that will call appropriate methods
// inside of a uvm_packer object.
//
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// Group -- NODOCS -- Packing Macros
//
// The packing macros assist users who implement the <uvm_object::do_pack>
// method. They help ensure that the pack operation is the exact inverse of the
// unpack operation. See also <Unpacking Macros>.
//
//| virtual function void do_pack(uvm_packer packer);
//|   `uvm_pack_int(cmd)
//|   `uvm_pack_int(addr)
//|   `uvm_pack_array(data)
//| endfunction
//
// The 'N' versions of these macros take a explicit size argument, which must
// be compile-time constant value greater than 0.
//------------------------------------------------------------------------------

//--------------------------------
// Group -- NODOCS -- Packing - With Size Info
//--------------------------------

// Macro -- NODOCS -- `uvm_pack_intN
//
// Pack an integral variable.
//
//| `uvm_pack_intN(VAR,SIZE)
//

// Group: Packing Macros
//
// The packing macros are implemented as described in section B.2.4 of the
// 1800.2 specification.
//
// The Accellera implementation adds an additional ~PACKER~ argument to 
// these macros with a default value of 'packer'.  This allows the macros
// to be used in environments with alternative packer names.
//
// For example, <`uvm_pack_intN> is defined in the LRM as
// | `define uvm_pack_intN(VAR,SIZE)
//
// Whereas the implementation is
// | `define uvm_pack_intN(VAR,SIZE,PACKER=packer)
//
// This allows for usage such as
// | function void pack_foo( uvm_packer other_packer );
// |   `uvm_pack_intN(foo, 32, other_packer)
// | endfunction : pack_foo
//
// @uvm-contrib This API is being considered for potential contribution to 1800.2


// @uvm-ieee 1800.2-2017 auto B.2.4.1
`define uvm_pack_intN(VAR,SIZE,PACKER=packer) \
  begin \
    bit __array[]; \
    { << bit { __array}} = VAR; \
    __array = new [SIZE] (__array); \
    PACKER.pack_bits(__array, SIZE); \
  end

// @uvm-ieee 1800.2-2017 auto B.2.4.2
`define uvm_pack_enumN(VAR,SIZE,PACKER=packer) \
   `uvm_pack_intN(VAR,SIZE,PACKER)



// @uvm-ieee 1800.2-2017 auto B.2.4.3
`define uvm_pack_sarrayN(VAR,SIZE,PACKER=packer) \
    begin \
    foreach (VAR `` [index]) \
      `uvm_pack_intN(VAR[index],SIZE,PACKER) \
    end



// @uvm-ieee 1800.2-2017 auto B.2.4.4
`define uvm_pack_arrayN(VAR,SIZE,PACKER=packer) \
    begin \
      `uvm_pack_intN(VAR.size(),32,PACKER) \
      `uvm_pack_sarrayN(VAR,SIZE,PACKER) \
    end



// @uvm-ieee 1800.2-2017 auto B.2.4.5
`define uvm_pack_queueN(VAR,SIZE,PACKER=packer) \
   `uvm_pack_arrayN(VAR,SIZE,PACKER)


//------------------------------
// Group -- NODOCS -- Packing - No Size Info
//------------------------------


// @uvm-ieee 1800.2-2017 auto B.2.4.6
`define uvm_pack_int(VAR,PACKER=packer) \
   `uvm_pack_intN(VAR,$bits(VAR),PACKER)

// uvm_pack_object
`define uvm_pack_object(VAR,PACKER=packer) \
  PACKER.pack_object_with_meta(VAR);

// @uvm-ieee 1800.2-2017 auto B.2.4.7
`define uvm_pack_enum(VAR,PACKER=packer) \
   `uvm_pack_enumN(VAR,$bits(VAR),PACKER)



// @uvm-ieee 1800.2-2017 auto B.2.4.8
`define uvm_pack_string(VAR,PACKER=packer) \
  PACKER.pack_string(VAR);



// @uvm-ieee 1800.2-2017 auto B.2.4.9
`define uvm_pack_real(VAR,PACKER=packer) \
  PACKER.pack_real(VAR);



// @uvm-ieee 1800.2-2017 auto B.2.4.10
`define uvm_pack_sarray(VAR,PACKER=packer)  \
   `uvm_pack_sarrayN(VAR,$bits(VAR[0]),PACKER)



// @uvm-ieee 1800.2-2017 auto B.2.4.11
`define uvm_pack_array(VAR,PACKER=packer) \
   `uvm_pack_arrayN(VAR,$bits(VAR[0]),PACKER)

`define uvm_pack_da(VAR,PACKER=packer) \
  `uvm_pack_array(VAR,PACKER)

// @uvm-ieee 1800.2-2017 auto B.2.4.12
`define uvm_pack_queue(VAR,PACKER=packer) \
   `uvm_pack_queueN(VAR,$bits(VAR[0]),PACKER)

//------------------------------------------------------------------------------
// Group -- NODOCS -- Unpacking Macros
//
// The unpacking macros assist users who implement the <uvm_object::do_unpack>
// method. They help ensure that the unpack operation is the exact inverse of
// the pack operation. See also <Packing Macros>.
//
//| virtual function void do_unpack(uvm_packer packer);
//|   `uvm_unpack_enum(cmd,cmd_t)
//|   `uvm_unpack_int(addr)
//|   `uvm_unpack_array(data)
//| endfunction
//
// The 'N' versions of these macros take a explicit size argument, which must
// be a compile-time constant value greater than 0.
//------------------------------------------------------------------------------

//----------------------------------
// Group -- NODOCS -- Unpacking - With Size Info
//----------------------------------


// @uvm-ieee 1800.2-2017 auto B.2.5.1
`define uvm_unpack_intN(VAR,SIZE,PACKER=packer) \
  begin \
    bit __array[] = new [SIZE]; \
    PACKER.unpack_bits(__array, SIZE); \
    __array = new [$bits(VAR)] (__array); \
    VAR = { << bit { __array }}; \
  end



// @uvm-ieee 1800.2-2017 auto B.2.5.2
`define uvm_unpack_enumN(VAR,SIZE,TYPE,PACKER=packer) \
  begin \
    bit __array[] = new [SIZE]; \
    PACKER.unpack_bits(__array, SIZE); \
    __array = new [$bits(VAR)] (__array); \
    VAR = TYPE'({ << bit { __array }}); \
  end



// @uvm-ieee 1800.2-2017 auto B.2.5.3
`define uvm_unpack_sarrayN(VAR,SIZE,PACKER=packer) \
    begin \
    foreach (VAR `` [i]) \
      `uvm_unpack_intN(VAR``[i], SIZE, PACKER) \
    end



// @uvm-ieee 1800.2-2017 auto B.2.5.4
`define uvm_unpack_arrayN(VAR,SIZE,PACKER=packer) \
    begin \
      int sz__; \
      `uvm_unpack_intN(sz__,32,PACKER) \
      VAR = new[sz__]; \
      `uvm_unpack_sarrayN(VAR,SIZE,PACKER) \
    end



// @uvm-ieee 1800.2-2017 auto B.2.5.5
`define uvm_unpack_queueN(VAR,SIZE,PACKER=packer) \
    begin \
      int sz__; \
      `uvm_unpack_intN(sz__,32,PACKER) \
      while (VAR.size() > sz__) \
        void'(VAR.pop_back()); \
      for (int i=0; i<sz__; i++) \
        `uvm_unpack_intN(VAR[i],SIZE,PACKER) \
    end


//--------------------------------
// Group -- NODOCS -- Unpacking - No Size Info
//--------------------------------



// @uvm-ieee 1800.2-2017 auto B.2.5.6
`define uvm_unpack_int(VAR,PACKER=packer) \
   `uvm_unpack_intN(VAR,$bits(VAR),PACKER)

// uvm_unpack_object
`define uvm_unpack_object(VAR,PACKER=packer) \
  begin \
    uvm_object __ref = VAR; \
    PACKER.unpack_object_with_meta(__ref); \
    if ((__ref != VAR) && !$cast(VAR,__ref)) begin \
      `uvm_fatal("UVM/UNPACK_EXT/OBJ_CAST_FAILED", \
                {"Could not cast object of type '", __ref.get_type_name(), \
                 "' into '", `"LVALUE`"}) \
    end \
  end


// @uvm-ieee 1800.2-2017 auto B.2.5.7
`define uvm_unpack_enum(VAR,TYPE,PACKER=packer) \
   `uvm_unpack_enumN(VAR,$bits(VAR),TYPE,PACKER)



// @uvm-ieee 1800.2-2017 auto B.2.5.8
`define uvm_unpack_string(VAR,PACKER=packer) \
  VAR = PACKER.unpack_string();


// @uvm-ieee 1800.2-2017 auto B.2.5.9
`define uvm_unpack_real(VAR,PACKER=packer) \
  VAR = PACKER.unpack_real();



// @uvm-ieee 1800.2-2017 auto B.2.5.10
`define uvm_unpack_sarray(VAR,PACKER=packer)  \
   `uvm_unpack_sarrayN(VAR,$bits(VAR[0]),PACKER)



// @uvm-ieee 1800.2-2017 auto B.2.5.11
`define uvm_unpack_array(VAR,PACKER=packer) \
   `uvm_unpack_arrayN(VAR,$bits(VAR[0]),PACKER)

// Implementation artifact.  Simplifies field macros.
`define uvm_unpack_da(VAR,PACKER=packer) \
  `uvm_unpack_array(VAR,PACKER)


// @uvm-ieee 1800.2-2017 auto B.2.5.12
`define uvm_unpack_queue(VAR,PACKER=packer) \
   `uvm_unpack_queueN(VAR,$bits(VAR[0]),PACKER)


//--

`define uvm_pack_aa_int_intN(VAR, SIZE, PACKER=packer) \
begin \
  `uvm_pack_intN(VAR.num(), 32, PACKER) \
  if (VAR.num()) begin \
    `uvm_pack_intN(SIZE, 32, PACKER) \
    foreach(VAR[i]) begin \
      `uvm_pack_intN(i, SIZE, PACKER) \
      `uvm_pack_int(VAR[i],PACKER) \
    end \
  end \
end

`define uvm_unpack_aa_int_intN(VAR, SIZE, PACKER=packer) \
begin \
  int __num__; \
  `uvm_unpack_intN(__num__, 32, PACKER) \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    bit[SIZE-1:0] __index__; \
    int __sz__; \
    `uvm_unpack_intN(__sz__, 32, PACKER) \
    if (SIZE != __sz__) \
      `uvm_error("UVM/UNPACK/AA_INT_SZ", $sformatf("Unpack size '%0d' different from pack size '%0d'", \
                                                   SIZE, \
                                                   __sz__)) \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_intN(__index__, SIZE, PACKER) \
      `uvm_unpack_int(VAR[__index__], PACKER) \
    end \
  end \
end
   
//--

`define uvm_pack_aa_object_intN(VAR, SIZE, PACKER=packer) \
begin \
  PACKER.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    PACKER.pack_field_int(SIZE, 32); \
    foreach(VAR[i]) begin \
      `uvm_pack_intN(i, SIZE, PACKER) \
      `uvm_pack_object(VAR[i], PACKER) \
    end \
  end \
end

`define uvm_unpack_aa_object_intN(VAR, SIZE, PACKER=packer) \
begin \
  int __num__; \
  `uvm_unpack_intN(__num__, 32, PACKER) \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    bit[SIZE-1:0] __index__; \
    int __sz__; \
    `uvm_unpack_intN(__sz__, 32, PACKER) \
    if (SIZE != __sz__) \
      `uvm_error("UVM/UNPACK/AA_INT_SZ", $sformatf("Size '%d' insufficient to store '%d' bits", \
                                                   SIZE, \
                                                   __sz__)) \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_intN(__index__, __sz__, PACKER) \
      `uvm_unpack_object(VAR[__index__],PACKER) \
    end \
  end \
end
   
//--

`define uvm_pack_aa_string_intN(VAR, SIZE, PACKER=packer) \
begin \
  PACKER.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    PACKER.pack_field_int(SIZE, 32); \
    foreach(VAR[i]) begin \
      `uvm_pack_intN(i, SIZE, PACKER) \
      `uvm_pack_string(VAR[i], PACKER) \
    end \
  end \
end

`define uvm_unpack_aa_string_intN(VAR, SIZE, PACKER=packer) \
begin \
  int __num__; \
  `uvm_unpack_intN(__num__, 32, PACKER) \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    bit[SIZE-1:0] __index__; \
    int __sz__; \
    `uvm_unpack_intN(__sz__, 32, PACKER) \
    if (SIZE != __sz__) \
      `uvm_error("UVM/UNPACK/AA_INT_SZ", $sformatf("Size '%d' insufficient to store '%d' bits", \
                                                   SIZE, \
                                                   __sz__)) \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_intN(__index__, __sz__, PACKER) \
      `uvm_unpack_string(VAR[__index__], PACKER) \
    end \
  end \
end
   
//--

`define uvm_pack_aa_object_string(VAR, PACKER=packer) \
begin \
  PACKER.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    foreach(VAR[i]) begin \
      `uvm_pack_string(i, PACKER) \
      `uvm_pack_object(VAR[i], PACKER) \
    end \
  end \
end

`define uvm_unpack_aa_object_string(VAR, PACKER=packer) \
begin \
  int __num__ = PACKER.unpack_field_int(32); \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    string __index__; \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_string(__index__, PACKER) \
      `uvm_unpack_object(VAR[__index__], PACKER) \
    end \
  end \
end

//--

`define uvm_pack_aa_int_string(VAR, PACKER=packer) \
begin \
  PACKER.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    foreach(VAR[i]) begin \
      `uvm_pack_string(i, PACKER) \
      `uvm_pack_int(VAR[i], PACKER) \
    end \
  end \
end

`define uvm_unpack_aa_int_string(VAR, PACKER=packer) \
begin \
  int __num__ = PACKER.unpack_field_int(32); \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    string __index__; \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_string(__index__, PACKER) \
      `uvm_unpack_int(VAR[__index__], PACKER) \
    end \
  end \
end

//--

`define uvm_pack_aa_string_string(VAR, PACKER=packer) \
begin \
  PACKER.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    foreach(VAR[i]) begin \
      `uvm_pack_string(i, PACKER) \
      `uvm_pack_string(VAR[i], PACKER) \
    end \
  end \
end

`define uvm_unpack_aa_string_string(VAR, PACKER=packer) \
begin \
  int __num__ = PACKER.unpack_field_int(32); \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    string __index__; \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_string(__index__, PACKER) \
      `uvm_unpack_string(VAR[__index__], PACKER) \
    end \
  end \
end

//--

`define uvm_pack_aa_int_enum(VAR, TYPE, PACKER=packer) \
begin \
  PACKER.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    foreach(VAR[i]) begin \
      `uvm_pack_enum(i, PACKER) \
      `uvm_pack_int(VAR[i], PACKER) \
    end \
  end \
end

`define uvm_unpack_aa_int_enum(VAR, TYPE, PACKER=packer) \
begin \
  int __num__ = PACKER.unpack_field_int(32); \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    TYPE __index__; \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_enum(__index__, TYPE, PACKER) \
      `uvm_unpack_int(VAR[__index__], PACKER) \
    end \
  end \
end
   
//--

`define uvm_pack_aa_object_enum(VAR, TYPE, PACKER=packer) \
begin \
  PACKER.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    foreach(VAR[i]) begin \
      `uvm_pack_enum(i, PACKER) \
      `uvm_pack_object(VAR[i], PACKER) \
    end \
  end \
end

`define uvm_unpack_aa_object_enum(VAR, TYPE, PACKER=packer) \
begin \
  int __num__ = PACKER.unpack_field_int(32); \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    TYPE __index__; \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_enum(__index__, TYPE, PACKER) \
      `uvm_unpack_object(VAR[__index__], PACKER) \
    end \
  end \
end
   
//--

`define uvm_pack_aa_string_enum(VAR, TYPE, PACKER=packer) \
begin \
  PACKER.pack_field_int(VAR.num(), 32); \
  if (VAR.num()) begin \
    foreach(VAR[i]) begin \
      `uvm_pack_intN(i, SIZE, PACKER) \
      `uvm_pack_string(VAR[i], PACKER) \
    end \
  end \
end

`define uvm_unpack_aa_string_enum(VAR, TYPE, PACKER=packer) \
begin \
  int __num__ = PACKER.unpack_field_int(32); \
  if (__num__ == 0) \
    VAR.delete(); \
  else begin \
    TYPE __index__; \
    for (int __i__ = 0; __i__ < __num__; __i__++) begin \
      `uvm_unpack_enum(__index__, TYPE, PACKER) \
      `uvm_unpack_string(VAR[__index__], PACKER) \
    end \
  end \
end
   
//--

`define uvm_pack_sarray_real(VAR, PACKER=packer) \
  foreach(VAR[index]) \
    `uvm_pack_real(VAR[index], PACKER)

`define m_uvm_pack_qda_real(VAR, PACKER=packer) \
  `uvm_pack_intN(VAR.size(), 32, PACKER) \
  `uvm_pack_sarray_real(VAR, PACKER)

`define uvm_pack_queue_real(VAR, PACKER=packer) \
  `m_uvm_pack_qda_real(VAR, PACKER)

`define uvm_pack_da_real(VAR, PACKER=packer) \
  `m_uvm_pack_qda_real(VAR, PACKER)

`define uvm_unpack_sarray_real(VAR, PACKER=packer) \
  foreach(VAR[index]) \
    `uvm_unpack_real(VAR[index], PACKER)

`define uvm_unpack_da_real(VAR, PACKER=packer) \
  begin \
    int tmp_size__; \
    `uvm_unpack_intN(tmp_size__, 32, PACKER) \
    VAR = new [tmp_size__]; \
    `uvm_unpack_sarray_real(VAR, PACKER) \
  end

`define uvm_unpack_queue_real(VAR, PACKER=packer) \
  begin \
    int tmp_size__; \
    `uvm_unpack_intN(tmp_size__, 32, PACKER) \
    while (VAR.size() > tmp_size__) \
      void'(VAR.pop_back()); \
    for (int i = 0; i < tmp_size__; i++) \
      `uvm_unpack_real(VAR[i], PACKER) \
  end

`endif //  `ifndef UVM_PACKER_DEFINES_SVH
