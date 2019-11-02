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
// ECC-protected memory model extension for RAL
//
// This example assumes 32 bits of user data and 4 bits of ECC code
// stored in a memory with 36-bit addressable words.
//

`include "vmm_ral.sv"


//
// Compute ECC code
//
class ecc_32_4;
   virtual function bit [3:0] compute(bit [31:0] data);
      compute = {^data[31:24],
                 ^data[23:16],
                 ^data[15: 8],
                 ^data[ 7: 0]};
   endfunction: compute
endclass: ecc_32_4

       

//
// Memory callback extension implementing ECC error injection.
// Errors can be injected when a memory location is written
// (i.e. the ECC error will be reported every time the location
// is read back) or it can be injected when a memory location is
// read (i.e. the ECC error may or may not be reported when the
// same location is subsequently read).
//
// This error injection model supports only single-bit errors, in
// either the data or ECC code itself.
//
// By default, errors are not injected. Errors can be injected at
// a specified rate by setting the 'error_rate' value to non-zero.
// A value of 'hFF indicates 100% error rate.
//
// This callback class works in tandem with the backdoor access
// class to allow direct access to the ECC code via the the backdoor.
// See ecc_mem0_bkdr class below.
//
class ecc_mem0_cb extends vmm_ral_mem_callbacks;

   bit [7:0] error_rate = 0;
   rand bit error_on_write;
   rand bit error_on_read;
   rand bit [6:0] error_on_bit;

   static local ecc_32_4 ecc = new;
   local bit [35:0] ecc_rdat;

   constraint valid {
      error_on_bit < 36;
   }

   constraint write_error_rate {
      error_on_write dist {0 :/ (255 - error_rate),
                           1 :/ error_rate};
   }
   constraint read_error_rate {
      error_on_read dist {0 :/ (255 - error_rate),
                          1 :/ error_rate};
   }

   virtual task post_write(vmm_ral_mem           mem,
                           bit [63:0]            offset,
                           bit [63:0]            wdat,
                           vmm_ral::path_e       path,
                           string                domain,
                           ref vmm_rw::status_e  status);
      bit [35:0] ecc_wdat;

      // No point in injecting random ECC error on write if
      // writing via backdoor WITH an ECC error
      if (path == vmm_ral::BACKDOOR && wdat[35:32] != 4'b0000) begin
         this.error_on_write = 1;
         return;
      end

      ecc_wdat = {this.ecc.compute(wdat), wdat[31:0]};
      this.randomize();
      if (this.error_on_write) begin
         ecc_wdat ^= 1'b1 << error_on_bit;
      end    
      tb_top.dut.mem0[offset] = ecc_wdat;
      
   endtask: post_write


   virtual task pre_read(vmm_ral_mem          mem,
                         ref bit [63:0]       offset,
                         ref vmm_ral::path_e  path,
                         ref string           domain);
      // No point in injecting ECC error on read if
      // reading via backdoor...
      if (path == vmm_ral::BACKDOOR) begin
         this.error_on_read = 0;
         return;
      end

      this.randomize();
      if (this.error_on_read) begin
         ecc_rdat = tb_top.dut.mem0[offset];
         tb_top.dut.mem0[offset] = ecc_rdat ^ (1'b1 << error_on_bit);
      end    
      
   endtask: pre_read


   virtual task post_read(input vmm_ral_mem       mem,
                          input bit [63:0]        offset,
                          ref   bit [63:0]        rdat,
                          input vmm_ral::path_e   path,
                          input string            domain,
                          ref   vmm_rw::status_e  status);
      // Remove the ECC error at the end of the read
      if (this.error_on_read) begin
         tb_top.dut.mem0[offset] = ecc_rdat;
      end    
   endtask: post_read
endclass: ecc_mem0_cb



//
// Backdoor accesses can include ECC information because
// the data value is always transfered as 64 bits.
// If the ECC-protected memory has addressable locations
// that are less than 64 bits, the additional bits can be used
// to carry the ECC information. In this example, the 32 bit
// data values are concatenated with a 4-bit ECC code yielding
// 36 bit transfers.
//
// The ECC information is represented using a validity
// indicator, not the ECC value. If the bit is cleared, the
// corresponding ECC bit is valid. If the bit is set, the
// corresponding ECC bit is invalid or will be corrupted.
//
// Note that backdoor accesses are subjected to the memory
// callbacks (see ecc_mem0_cb class above) before they are
// physically executed in this backdoor access class.
//
class ecc_mem0_backdoor extends vmm_ral_mem_backdoor;
   static local ecc_32_4 ecc = new;
    
   virtual task write(output vmm_rw::status_e status,
                      input  bit [63:0]       offset,
                      input  bit [63:0]       data,
                      input  int              data_id,
                      input  int              scenario_id,
                      input  int              stream_id);
      // Corrupt ECC bit if it is set in the data to write
      data[35:32] = this.ecc.compute(data[31:0]) ^ data[35:32];
      tb_top.dut.mem0[offset] = data;
      status = vmm_rw::IS_OK;
   endtask: write

   virtual task read(output vmm_rw::status_e status,
                     input  bit [63:0]       offset,
                     output bit [63:0]       data,
                     input  int              data_id,
                     input  int              scenario_id,
                     input  int              stream_id);
      // Report invalid ECC bits
      data = tb_top.dut.mem0[offset];
      data[35:32] = this.ecc.compute(data[31:0]) ^ data[35:32];
      status = vmm_rw::IS_OK;
   endtask: read
endclass: ecc_mem0_backdoor



//
// Fake DUT to enable error-free compilation
//
module dut();
   reg [35:0] mem0[1023];
endmodule

module tb_top();

dut dut();

endmodule
