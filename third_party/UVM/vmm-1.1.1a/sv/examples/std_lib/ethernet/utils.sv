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


//
// Ethernet utility class
//
class eth_utils;

   local static bit [31:0] crc_table[256];
   local static logic init;

   /*extern*/ function new();
   if (this.init !== 1'b1) begin
      bit [7:0] i;
      
      // Initialize the CRC syndrom table
      i = 0;
      repeat (256) begin
         bit [31:0] r;
         
         r = {i[0], i[1], i[2], i[3], i[4], i[5], i[6], i[7]} << 24;
         repeat (8) begin
            if (r[31]) r = (r << 1) ^ 32'h04C11DB7;
            else r <<= 1;
         end
         this.crc_table[i] =
            {r[00], r[01], r[02], r[03], r[04], r[05], r[06], r[07],
             r[08], r[09], r[10], r[11], r[12], r[13], r[14], r[15],
             r[16], r[17], r[18], r[19], r[20], r[21], r[22], r[23],
             r[24], r[25], r[26], r[27], r[28], r[29], r[30], r[31]};
         i++;
      end
      this.init = 1'b1;
   end // if (this.init !== 1'b1)
endfunction: new

   extern function eth_frame bytes_to_frame(vmm_log               log,
                                            const ref logic [7:0] bytes[],
                                            integer               n_bytes,
                                            eth_frame             factory);

   extern function void frame_to_bytes(/*const*/ eth_frame frame,
                                       ref logic [7:0] bytes[]);

   extern function bit [31:0] compute_crc32(const ref logic [7:0] bytes[],
                                            input int unsigned   offset = 0,
                                            input integer        len    = -1);
endclass: eth_utils


/*function eth_utils::new();*/

   
function eth_frame eth_utils::bytes_to_frame(vmm_log               log,
                                             const ref logic [7:0] bytes[],
                                             integer               n_bytes,
                                             eth_frame             factory);
   integer i = 0;
   integer start_offset;
   logic [31:0] fcs;

   bytes_to_frame = null;
   start_offset = 0;

   // Ignore the preamble & SFD
   while (i < n_bytes && bytes[i] === 8'b01010101) i++;
   if (bytes[i] === 8'b11010101) start_offset = i+1;

   // A frame must be at LEAST 18 bytes long (and even that
   // would violate the minimum frame length)
   if (n_bytes - start_offset < 18) begin
      // That is not an error. Could be a frame that was
      // aborted due to collision
      `vmm_debug(log, "Received frame was <18 bytes long!");
      return null;
   end

   // The last 4 bytes are supposed to be the FCS
   fcs = {bytes[n_bytes-4], bytes[n_bytes-3],
          bytes[n_bytes-2], bytes[n_bytes-1]};
   begin
      bit [31:0] crc;
      crc = this.compute_crc32(bytes, start_offset, n_bytes-start_offset-4);
      if (crc !== fcs) begin
         // Bad FCS values indicate partial frames or
         // jammed frames due to collisions. Not an error either
         `vmm_debug(log, $psprintf("Received frame with bad FCS: %h instead of %h", fcs, crc));
         return null;
      end
   end

   // Example 4-62
   // Looks like we have a valid frame!
   $cast(bytes_to_frame, factory.copy());
     
   void'(bytes_to_frame.byte_unpack(bytes, start_offset,
                                    n_bytes - start_offset - 4));

   // FCS must be good
   bytes_to_frame.fcs = 32'h0;
endfunction: bytes_to_frame
 

// Example 4-37
function void eth_utils::frame_to_bytes(/*const*/ eth_frame frame,
                                        ref logic [7:0] bytes[]);
   integer i;

   // Preallocate the necessary number of bytes
   i = frame.byte_size() + 4;
   if (i < 64) i = 64;
   bytes = new [i + 8];

   // Preamble
   for (i = 0; i < 7; i++) begin
      bytes[i] = 8'b01010101;
   end
   // SFD
   bytes[7] = 8'b11010101;
   i = frame.byte_pack(bytes, 8) + 8;

   // Padding?
   while (i < 64/*max*/  - 4/*FCS*/ + 8/*Preamble*/) begin
      bytes[i++] = $random;
   end

   // Append the FCS
   // Example 4-37
   {bytes[i], bytes[i+1], bytes[i+2], bytes[i+3]} =
      this.compute_crc32(bytes, 8, i-8) ^ frame.fcs;

endfunction: frame_to_bytes


function bit [31:0] eth_utils::compute_crc32(const ref logic [7:0] bytes[],
                                             input int unsigned    offset = 0,
                                             input integer         len    = -1);
   logic [31:0] crc;
   integer      i;

   if (len < 0) len = bytes.size() - offset;

   crc = 32'hFFFFFFFF;
   for (i = offset; i < offset+len && i < bytes.size(); i++) begin
      // If any bit of the packed data is 'x', it
      // will cause a run-time failure because of an
      // invalid index in crc_table[]
      if ((^bytes[i]) === 1'bx) begin
         return 32'hXXXXXXXX;
      end
      crc = this.crc_table[crc[7:0] ^ bytes[i]] ^
                    {8'h00, crc[31:8]};
   end

   // Invert final result
   crc = ~crc;

   // Swap bytes to obtain transmit order
   compute_crc32[31:24] = crc[ 7: 0];
   compute_crc32[23:16] = crc[15: 8];
   compute_crc32[15: 8] = crc[23:16];
   compute_crc32[ 7: 0] = crc[31:24];
endfunction: compute_crc32
