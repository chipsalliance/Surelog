// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    All Rights Reserved Worldwide
// 
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
// 
//        http://www.apache.org/licenses/LICENSE-2.0
// 
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
// 


class fifo_trans extends vmm_data;

  static vmm_log log = new ("fifo_trans", "class") ;
    
  // Local Data Members
   rand logic [15:0] data;
   rand logic [15:0] wr_data_rate;
   rand logic [15:0] rd_data_rate;                                                                       
   constraint reasonable { 
     wr_data_rate > 0; wr_data_rate < 10; 
     rd_data_rate > 0; rd_data_rate < 10; 
   }    
  // Constructor
  extern function new();

  // VMM Standard Methods
  extern virtual function string   psdisplay(string prefix = "");
    
  extern virtual function vmm_data allocate ();
  extern virtual function vmm_data copy     (vmm_data to = null);
  extern virtual function bit      compare  (vmm_data to,
                                             output string diff,
                                             input int kind = -1);
    
  extern virtual function bit      is_valid (bit silent = 1,
                                             int kind = -1);
    
  extern virtual function int unsigned byte_size  (int kind = -1);
  extern virtual function int unsigned byte_pack  (ref logic [7:0] bytes[],
                                                   input int unsigned offset = 0,
                                                   input int  kind = -1);
  extern virtual function int unsigned byte_unpack(const ref logic [7:0] bytes[],
                                                   input int unsigned offset = 0,
                                                   input int len  = -1,
                                                   input int kind = -1);
endclass: fifo_trans

//-----------------------------------------------------------------------------
// VMM Macros - Channel and Atomic Generator
//-----------------------------------------------------------------------------

`vmm_channel(fifo_trans)
`vmm_atomic_gen(fifo_trans, "FIFO Atomic Gen")

//-----------------------------------------------------------------------------
// new() - Constructor
//-----------------------------------------------------------------------------

function fifo_trans::new();

  super.new(this.log);

endfunction: new

//-----------------------------------------------------------------------------
// allocate() - VMM
//-----------------------------------------------------------------------------

function vmm_data fifo_trans::allocate();

  // Allocate a new object of this type, and return a handle to it
  fifo_trans i = new();
  allocate = i;
    
endfunction: allocate

//-----------------------------------------------------------------------------
// copy() - VMM
//-----------------------------------------------------------------------------

function vmm_data fifo_trans::copy(vmm_data to = null);
    
  fifo_trans cpy;

  // Allocate a new object if needed, check the type if 'to' specified
  if (to == null)
    cpy = new();
  else if (!$cast(cpy, to)) begin
    `vmm_error(this.log, "Cannot copy to non-fifo_trans instance");
    return null;
  end

  // Copy the data fields into the 'to' object and return cpy
  copy_data(cpy);

  cpy.data = this.data;
  cpy.wr_data_rate = this.wr_data_rate; 
  cpy.rd_data_rate = this.rd_data_rate;                 

  copy = cpy;

endfunction: copy


//-----------------------------------------------------------------------------
// compare - VMM
//-----------------------------------------------------------------------------

function bit fifo_trans::compare(vmm_data   to,
                                 output string diff,
                                 input int  kind = -1);
   fifo_trans pkt;
   compare = 1;

   // Check the type is correct    
   if (to == null || !$cast(pkt, to)) begin
      `vmm_error(this.log, "Cannot compare to non-fifo_trans instance");
      return 0;
   end

   if (pkt.data !== this.data) begin   
      $sformat(diff, "data (%1b !== %1b)", this.data, pkt.data); 
      return 0;
   end
endfunction: compare

//-----------------------------------------------------------------------------
// psdisplay() - VMM
//-----------------------------------------------------------------------------
    
function string fifo_trans::psdisplay(string prefix = "");
   $sformat(psdisplay, "%swr_dr=%02d rd_dr=%02d data=%h",
           prefix, this.wr_data_rate, this.rd_data_rate, this.data);
   return psdisplay;
endfunction: psdisplay 

  
//-----------------------------------------------------------------------------
// is_valid() - VMM
//-----------------------------------------------------------------------------

function bit fifo_trans::is_valid(bit silent = 1,
                                 int kind = -1);
    is_valid = 1;

endfunction: is_valid

//-----------------------------------------------------------------------------
// byte_size() - VMM
//-----------------------------------------------------------------------------

function int unsigned fifo_trans::byte_size(int kind = -1);

    byte_size = 6;
endfunction: byte_size


//-----------------------------------------------------------------------------
// byte_pack() - VMM
//-----------------------------------------------------------------------------

function int unsigned fifo_trans::byte_pack(ref logic [7:0]    bytes[],
                                             input int unsigned offset = 0,
                                             input int          kind = -1);
   bytes = new[offset +  byte_size()] (bytes);

   bytes[offset++] = wr_data_rate[7:0];
   bytes[offset++] = wr_data_rate[15:8];
   bytes[offset++] = rd_data_rate[7:0];
   bytes[offset++] = rd_data_rate[15:8];
   bytes[offset++] = data[7:0];
   bytes[offset++] = data[15:8];

   return byte_size();
endfunction: byte_pack

//-----------------------------------------------------------------------------
// byte_unpack() - VMM
//-----------------------------------------------------------------------------

function int unsigned fifo_trans::byte_unpack(const ref logic [7:0] bytes[],
                                             input int unsigned    offset = 0,
                                             input int             len = -1,
                                             input int             kind = -1);
   wr_data_rate = { bytes[offset+1], bytes[offset] };
   offset += 2;
   rd_data_rate = { bytes[offset+1], bytes[offset] };   
   offset += 2;
   data = { bytes[offset+1] , bytes[offset] }; 

   return byte_size();   // Return the number of bytes unpacked
endfunction: byte_unpack
