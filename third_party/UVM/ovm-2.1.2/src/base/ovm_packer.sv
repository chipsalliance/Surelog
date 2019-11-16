// $Id: ovm_packer.sv,v 1.15 2009/10/30 15:29:21 jlrose Exp $
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

`include "base/ovm_packer.svh"

//-----------------------------------------------------------------------------
//
// ovm_packer
//
//-----------------------------------------------------------------------------

// NOTE- max size limited to BITSTREAM bits parameter (default: 4096)


// index_ok
// --------

function void ovm_packer::index_error(int index, string id, int sz);
    ovm_report_error("PCKIDX", 
        $psprintf("index %0d for get_%0s too large; valid index range is 0-%0d.",
                  index,id,((m_packed_size+sz-1)/sz)-1), OVM_NONE);
endfunction


// enough_bits
// -----------

function bit ovm_packer::enough_bits(int needed, string id);
  if ((m_packed_size - count) < needed) begin
    ovm_report_error("PCKSZ",
        $psprintf("%0d bits needed to unpack %0s, yet only %0d available.",
                  needed, id, (m_packed_size - count)), OVM_NONE);
    return 0;
  end
  return 1;
endfunction


// get_packed_size
// ---------------

function int ovm_packer::get_packed_size();
  return m_packed_size;
endfunction


// set_packed_size
// ---------------

function void ovm_packer::set_packed_size();
  m_packed_size = count;
  count = 0;
endfunction


// reset
// -----

function void ovm_packer::reset();
  count = 0;
  m_bits = 0;
  m_packed_size = 0;
endfunction


// get_packed_bits
// ---------------

function ovm_pack_bitstream_t ovm_packer::get_packed_bits();
  //bits = m_bits;
  return m_bits;
endfunction


// get_bits
// --------

function void ovm_packer::get_bits(ref bit unsigned bits[]);
  bits = new[m_packed_size];
  for (int i=0;i<m_packed_size;i++)
    bits[i] = m_bits[i];
endfunction


// get_bytes
// ---------

function void ovm_packer::get_bytes(ref byte unsigned bytes[]);
  int sz;
  byte v;
  sz = (m_packed_size+7) / 8;
  bytes = new[sz];
  for (int i=0;i<sz;i++) begin
    if (i != sz-1 || (m_packed_size % 8) == 0) 
      v = m_bits[ i*8 +: 8 ];
    else
      v = m_bits[ i*8 +: 8 ] & ('hFF >> (8-(m_packed_size%8)));
    if(big_endian) begin
      byte tmp; tmp = v;
      for(int j=0; j<8; ++j) v[j] = tmp[7-j];
    end
    bytes[i] = v;
  end
endfunction


// get_ints
// --------

function void ovm_packer::get_ints(ref int unsigned ints[]);
  int sz, v;
  sz = (m_packed_size+31) / 32;
  ints = new[sz];
  for (int i=0;i<sz;i++) begin
    if (i != sz-1 || (m_packed_size % 32) == 0) 
      v = m_bits[ i*32 +: 32 ];
    else
      v = m_bits[ i*32 +: 32 ] & ('hFFFFFFFF >> (32-(m_packed_size%32)));
    if(big_endian) begin
      int tmp; tmp = v;
      for(int j=0; j<32; ++j) v[j] = tmp[31-j];
    end
    ints[i] = v;
  end
endfunction


// put_bits
// --------

function void ovm_packer::put_bits (ref bit bitstream []);

  int bit_size;

  bit_size = bitstream.size();

  if(big_endian)
    for (int i=bit_size-1;i>=0;i--)
      m_bits[i] = bitstream[i];
  else
    for (int i=0;i<bit_size;i++)
      m_bits[i] = bitstream[i];

  m_packed_size = bit_size;
  count = 0;
 
endfunction

// put_bytes
// ---------

function void ovm_packer::put_bytes (ref byte unsigned bytestream []);

  int byte_size;
  int index;
  byte unsigned b;

  byte_size = bytestream.size();
  index = 0;
  for (int i=0;i<byte_size;i++) begin
    b = bytestream[i];
    if(big_endian) begin
      byte unsigned tb; tb = b;
      for(int j=0;j<8;++j) b[j] = tb[7-j];
    end
    m_bits[index +:8] = b;
    index += 8;
  end

  m_packed_size = byte_size*8;
  count = 0;
endfunction


// put_ints
// --------

function void ovm_packer::put_ints (ref int unsigned intstream []);

  int int_size;
  int index;
  int unsigned v;

  int_size = intstream.size();

  index = 0;
  for (int i=0;i<int_size;i++) begin
    v = intstream[i];
    if(big_endian) begin
      int unsigned tv; tv = v;
      for(int j=0;j<32;++j) v[j] = tv[31-j];
    end
    m_bits[index +:32] = v;
    index += 32;
  end

  m_packed_size = int_size*32;
  count = 0;
endfunction




// get_bit
// -------

function bit unsigned ovm_packer::get_bit(int unsigned index);
  if (index >= m_packed_size)
    index_error(index, "bit",1);
  return m_bits[index];
endfunction


// get_byte
// --------

function byte unsigned ovm_packer::get_byte(int unsigned index);
  if (index >= (m_packed_size+7)/8)
    index_error(index, "byte",8);
  return m_bits[index*8 +: 8];
endfunction


// get_int
// -------

function int unsigned ovm_packer::get_int(int unsigned index);
  if (index >= (m_packed_size+31)/32)
    index_error(index, "int",32);
  return m_bits[(index*32) +: 32];
endfunction


// PACK


// pack_object
// ---------

function void ovm_packer::pack_object(ovm_object value);

  if(scope.in_hierarchy(value)) begin
    `ifdef INCA
    ovm_report_warning("CYCFND", $psprintf("Cycle detected for object @%0d during pack", this), OVM_NONE);
    `else
    ovm_report_warning("CYCFND", $psprintf("Cycle detected during pack"), OVM_NONE);
    `endif
    return;
  end

  if((policy != OVM_REFERENCE) && (value != null) ) begin
      if(use_metadata == 1) begin
        m_bits[count +: 4] = 1;
        count += 4; // to better debug when display packed bits in hexidecimal
      end
      scope.down(value.get_name(), value);
      value.m_field_automation(null, OVM_PACK,"");
      value.do_pack(this);
      scope.up(value);
  end
  else if(use_metadata == 1) begin
    m_bits[count +: 4] = 0;
    count += 4;
  end
endfunction

  
// pack_real
// ---------

function void ovm_packer::pack_real(real value);
  pack_field_int($realtobits(value), 64);
endfunction
  

// pack_time
// ---------

function void ovm_packer::pack_time(time value);
  pack_field_int(value, 64);
  //m_bits[count +: 64] = value; this overwrites endian adjustments
endfunction
  

// pack_field
// ----------

function void ovm_packer::pack_field(ovm_bitstream_t value, int size);
  for (int i=0; i<size; i++)
    if(big_endian == 1)
      m_bits[count+i] = value[size-1-i];
    else
      m_bits[count+i] = value[i];
  count += size;
endfunction
  

// pack_field_int
// --------------

function void ovm_packer::pack_field_int(logic [63:0] value, int size);
  for (int i=0; i<size; i++)
    if(big_endian == 1)
      m_bits[count+i] = value[size-1-i];
    else
      m_bits[count+i] = value[i];
  count += size;
endfunction
  

// pack_string
// -----------

function void ovm_packer::pack_string(string value);
  byte b;
  foreach (value[index]) begin
    if(big_endian == 0)
      m_bits[count +: 8] = value[index];
    else begin
      b = value[index];
      for(int i=0; i<8; ++i)
        m_bits[count+i] = b[7-i];
    end 
    count += 8;
  end
  if(use_metadata == 1) begin
    m_bits[count +: 8] = 0;
    count += 8;
  end
endfunction 


// UNPACK


// is_null
// -------

function bit ovm_packer::is_null();
  return (m_bits[count+:4]==0);
endfunction

// unpack_object
// -------------

function void ovm_packer::unpack_object_ext(inout ovm_object value);
  unpack_object(value);
endfunction

function void ovm_packer::unpack_object(ovm_object value);

  byte is_non_null; is_non_null = 1;

  if(scope.in_hierarchy(value)) begin
    `ifdef INCA
    ovm_report_warning("CYCFND", $psprintf("Cycle detected for object @%0d during unpack", this), OVM_NONE);
    `else
    ovm_report_warning("CYCFND", $psprintf("Cycle detected during unpack", this), OVM_NONE);
    `endif
    return;
  end

  if(use_metadata == 1) begin
    is_non_null = m_bits[count +: 4];
    count+=4;
  end

  // NOTE- policy is a _pack_ policy, not unpack policy;
  //       and you can't pack an object by REFERENCE
  if (value != null)begin
    if (is_non_null > 0) begin
      scope.down(value.get_name(), value);
      value.m_field_automation(null, OVM_UNPACK,"");
      value.do_unpack(this);
      scope.up(value);
    end
    else begin
      // TODO: help do_unpack know whether unpacked result would be null
      //       to avoid new'ing unnecessarily;
      //       this does not nullify argument; need to pass obj by ref
    end
  end
  else if ((is_non_null != 0) && (value == null)) begin
     ovm_report_error("UNPOBJ","can not unpack into null object", OVM_NONE);
     return;
  end

endfunction

  
// unpack_real
// -----------

function real ovm_packer::unpack_real();
  if (enough_bits(64,"real")) begin
    return $bitstoreal(unpack_field_int(64));
  end
endfunction
  

// unpack_time
// -----------

function time ovm_packer::unpack_time();
  if (enough_bits(64,"time")) begin
    return unpack_field_int(64);
  end
endfunction
  

// unpack_field
// ------------

function ovm_bitstream_t ovm_packer::unpack_field(int size);
  unpack_field = 'b0;
  if (enough_bits(size,"integral")) begin
    count += size;
    for (int i=0; i<size; i++)
      if(big_endian == 1)
        unpack_field[i] = m_bits[count-i-1];
      else
        unpack_field[i] = m_bits[count-size+i];
  end
endfunction
  

// unpack_field_int
// ----------------

function logic[63:0] ovm_packer::unpack_field_int(int size);
  unpack_field_int = 'b0;
  if (enough_bits(size,"integral")) begin
    count += size;
    for (int i=0; i<size; i++)
      if(big_endian == 1)
        unpack_field_int[i] = m_bits[count-i-1];
      else
        unpack_field_int[i] = m_bits[count-size+i];
  end
endfunction
  

// unpack_string
// -------------

// If num_chars is not -1, then the user only wants to unpack a
// specific number of bytes into the string.
function string ovm_packer::unpack_string(int num_chars=-1);
  byte b;
  bit  is_null_term; // Assumes a null terminated string
  int i; i=0;
  if(num_chars == -1) is_null_term = 1;
  else is_null_term = 0;

  while(enough_bits(8,"string") && 
        ((m_bits[count+:8] != 0) || (is_null_term == 0)) &&
        ((i<num_chars)||(is_null_term==1)) )
  begin
    // silly, because can not append byte/char to string
    unpack_string = {unpack_string," "};
    if(big_endian == 0)
      unpack_string[i] = m_bits[count +: 8];
    else begin
      for(int j=0; j<8; ++j)
        b[7-j] = m_bits[count+j];
      unpack_string[i] = b;
    end 
    count += 8;
    ++i;
  end
  if(enough_bits(8,"string"))
    count += 8;
endfunction 



