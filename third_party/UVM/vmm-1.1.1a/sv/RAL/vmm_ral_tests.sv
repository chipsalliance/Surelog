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


class vmm_ral_tests;

   extern `VMM_STATIC_M task hw_reset(vmm_ral_block blk,
                                      string        domain,
                                      vmm_log       log);

   extern `VMM_STATIC_M task bit_bash(vmm_ral_block blk,
                                      string        domain,
                                      vmm_log              log);

   extern `VMM_STATIC_M task mem_walk(vmm_ral_block blk,
                                      string        domain,
                                      vmm_log       log);

   extern `VMM_STATIC_M task reg_access(vmm_ral_block blk,
                                        vmm_log       log);

   extern `VMM_STATIC_M task mem_access(vmm_ral_block blk,
                                        vmm_log       log);

   extern `VMM_STATIC_M task shared_access(vmm_ral_block blk,
                                           vmm_log       log);


   extern local `VMM_STATIC_M task bash_kth_bit(vmm_log                       log,
                                                vmm_ral_reg                   regs,
                                                int                           k,
                                                vmm_ral::access_e             mode,
                                                string                        domain,
                                                bit [`VMM_RAL_DATA_WIDTH-1:0] wo_mask);
endclass: vmm_ral_tests


task vmm_ral_tests::hw_reset(vmm_ral_block blk,
                             string        domain,
                             vmm_log       log);
   vmm_ral_reg regs[];

   if(blk == null)
   begin
     `vmm_error(log, $psprintf("vmm_ral_tests::hw_reset - Null argument provided for vmm_ral_block"));
     return;
   end
   // Iterate over all registers, checking the reset values
   blk.get_registers(regs, domain);
   foreach (regs[i]) begin
      string domains[];

      // Registers with some attributes are not to be tested
      if (regs[i].get_attribute("NO_RAL_TESTS") != "" ||
	  regs[i].get_attribute("NO_HW_RESET_TEST") != "") continue;
	
      // Registers may be accessible from multiple physical interfaces (domains)
      regs[i].get_domains(domains);

      // Verify the initial (reset) value in each domain
      foreach (domains[j]) begin
         vmm_rw::status_e status;
         bit [`VMM_RAL_DATA_WIDTH-1:0] v;
      
         `vmm_note(log, $psprintf("Verifying reset value of register %s in domain \"%s\"...",
                                  regs[i].get_fullname(), domains[j]));

         regs[i].mirror(status, vmm_ral::VERB, vmm_ral::BFM, domains[j]);
         if (status != vmm_rw::IS_OK) begin
            `vmm_error(log, $psprintf("Status was %s when reading reset value of register \"%s\" through domain \"%s\".",
                                      status.name(), regs[i].get_fullname(), domains[j]));
         end
      end
   end
endtask: hw_reset



task vmm_ral_tests::bit_bash(vmm_ral_block blk,
                             string        domain,
                             vmm_log       log);
   vmm_ral_reg regs[];

   if(blk == null)
   begin
     `vmm_error(log, $psprintf("vmm_ral_tests::bit_bash - Null argument provided for vmm_ral_block"));
     return;
   end

   // Iterate over all registers, trying to modify read-only bits
   // and making sure read-write bits can be set and cleared
   blk.get_registers(regs, domain);
   foreach (regs[i]) begin
      vmm_ral_field fields[];
      vmm_ral::access_e mode[`VMM_RAL_DATA_WIDTH];
      string domains[];
      bit [`VMM_RAL_DATA_WIDTH-1:0] wo_mask;
      bit [`VMM_RAL_DATA_WIDTH-1:0] reset_val;
      int n_bits;

      // Registers with some attributes are not to be tested
      if (regs[i].get_attribute("NO_RAL_TESTS") != "" ||
	  regs[i].get_attribute("NO_BIT_BASH_TEST") != "") continue;
	
      n_bits = regs[i].get_n_bytes() * 8;

      // Let's see what kind of bits we have...
      regs[i].get_fields(fields);

      // Registers may be accessible from multiple physical interfaces (domains)
      regs[i].get_domains(domains);

      // Bash the bits in the register via each domain
      foreach (domains[j]) begin
         vmm_rw::status_e status;
         bit [`VMM_RAL_DATA_WIDTH-1:0] val, exp, v, other;
         int next_lsb;

         next_lsb = 0;
         wo_mask = '1;
         foreach (fields[k]) begin
            int lsb, w;

            lsb = fields[k].get_lsb_pos_in_register();
            w   = fields[k].get_n_bits();

            // Any unused bits on the right side of the LSB?
            while (next_lsb < lsb) begin
               mode[next_lsb++] = vmm_ral::RO;
            end

            repeat (w) begin
               mode[next_lsb] = fields[k].get_access(domains[j]);
               if (mode[next_lsb] == vmm_ral::WO) wo_mask[next_lsb] = 1'b0;
               next_lsb++;
            end
         end
         // Any unused bits on the left side of the MSB?
         while (next_lsb < 64) begin
            mode[next_lsb++] = vmm_ral::RO;
         end

         `vmm_note(log, $psprintf("Verifying bits in register %s in domain \"%s\"...",
                                  regs[i].get_fullname(), domains[j]));

         // The mirror still contains initial value
         reset_val = regs[i].get();

         // But the mirrored value of any WO bits will read back
         // as all zeroes via the frontdoor...
         reset_val &= wo_mask;

         regs[i].read(status, val, vmm_ral::BFM, domains[j]);
         if (status != vmm_rw::IS_OK) begin
            `vmm_error(log, $psprintf("Status was %s when reading register \"%s\" through domain \"%s\".",
                                      status, regs[i].get_fullname(), domains[j]));
         end

         if (val !== reset_val) begin
            `vmm_error(log, $psprintf("Initial value of register \"%s\" ('h%h) not %s ('h%h)",
                                      regs[i].get_fullname(), val,
                                      (j == 0) ? "reset value" : "as expected",
                                      reset_val));
         end

         // Bash the kth bit
         other = 0;
         for (int k = 0; k < n_bits; k++) begin

            // Cannot test unpredictable bit behavior
            if (mode[k] >= vmm_ral::DC) begin
               other[k] = 1;
               continue;
            end

            bash_kth_bit(log, regs[i], k, mode[k], domains[j], wo_mask);
         end

         // Write the complement of the reset value
         // Except in the "OTHER" and "USERx" bits
         val = reset_val ^ ~other;
         
         regs[i].write(status, val, vmm_ral::BFM, domains[j]);
         if (status != vmm_rw::IS_OK) begin
            `vmm_error(log, $psprintf("Status was %s when writing to register \"%s\" through domain \"%s\".",
                                      status, regs[i].get_fullname(), domains[j]));
         end
   
         exp = regs[i].get() & wo_mask;
         regs[i].read(status, v, vmm_ral::BFM, domains[j]);
         if (status != vmm_rw::IS_OK) begin
            `vmm_error(log, $psprintf("Status was %s when reading register \"%s\" through domain \"%s\".",
                                      status, regs[i].get_fullname(), domains[j]));
         end
   
         if (v !== exp) begin
            `vmm_error(log, $psprintf("Writing 'h%h to register \"%s\" with initial value 'h%h yielded 'h%h instead of 'h%h",
                                      val, regs[i].get_fullname(), reset_val, v, exp));
         end
      end
   end
endtask: bit_bash


task vmm_ral_tests::bash_kth_bit(vmm_log                       log,
                                 vmm_ral_reg                   regs,
                                 int                           k,
                                 vmm_ral::access_e             mode,
                                 string                        domain,
                                 bit [`VMM_RAL_DATA_WIDTH-1:0] wo_mask);
   vmm_rw::status_e status;
   bit [`VMM_RAL_DATA_WIDTH-1:0] val, exp, v;
   bit bit_val;
   if(regs == null)
   begin
     `vmm_error(log, $psprintf("vmm_ral_tests::bash_kth_bit - Null argument provided for vmm_ral_reg"));
     return;
   end

   `vmm_note(log, $psprintf("...Bashing %s bit #%0d", mode.name(), k));

   repeat (2) begin
      val = regs.get();
      v   = val;
      exp = val;
      val[k] = ~val[k];
      bit_val = val[k];

      regs.write(status, val, vmm_ral::BFM, domain);
      if (status != vmm_rw::IS_OK) begin
         `vmm_error(log, $psprintf("Status was %s when writing to register \"%s\" through domain \"%s\".",
                                   status, regs.get_fullname(), domain));
      end

      exp = regs.get() & wo_mask;
      regs.read(status, val, vmm_ral::BFM, domain);
      if (status != vmm_rw::IS_OK) begin
         `vmm_error(log, $psprintf("Status was %s when reading register \"%s\" through domain \"%s\".",
                                   status, regs.get_fullname(), domain));
      end
   
      if (val !== exp) begin
         `vmm_error(log, $psprintf("Writing a %b in bit #%0d of register \"%s\" with initial value 'h%h yielded 'h%h instead of 'h%h",
                                   bit_val, k, regs.get_fullname(), v, val, exp));
      end
   end
endtask: bash_kth_bit


task vmm_ral_tests::mem_walk(vmm_ral_block blk,
                             string        domain,
                             vmm_log       log);
   vmm_ral_mem mems[];

   if(blk == null)
   begin
     `vmm_error(log, $psprintf("vmm_ral_tests::mem_walk - Null argument provided for vmm_ral_block"));
     return;
   end

   // Walk over all RW memories
   blk.get_memories(mems, domain);
   foreach (mems[i]) begin
      vmm_ral::access_e mode;
      string domains[];
      int n_bits;

      // Memories with some attributes are not to be tested
      if (mems[i].get_attribute("NO_RAL_TESTS") != "" ||
	  mems[i].get_attribute("NO_MEM_WALK_TEST") != "") continue;
	
      n_bits = mems[i].get_n_bits();

      // Memories may be accessible from multiple physical interfaces (domains)
      mems[i].get_domains(domains);

      // Walk the memory via each domain
      foreach (domains[j]) begin
         vmm_rw::status_e status;
         bit [`VMM_RAL_DATA_WIDTH-1:0] val, exp, v;
   
         // Only deal with RW memories
         if (mems[i].get_access(domains[j]) != vmm_ral::RW) continue;

         `vmm_note(log, $psprintf("Walking memory %s in domain \"%s\"...",
                                  mems[i].get_fullname(), domains[j]));

         // The walking process is, for address k:
         // - Write ~k
         // - Read k-1 and expect ~(k-1) if k > 0
         // - Write k-1 at k-1
         // - Read k and expect ~k if k == last address
         for (int k = 0; k < mems[i].get_size(); k++) begin
            mems[i].write(status, k, ~k, vmm_ral::BFM, domains[j]);
            if (status != vmm_rw::IS_OK) begin
               `vmm_error(log, $psprintf("Status was %s when writing \"%s[%0d]\" through domain \"%s\".",
                                         status.name(), mems[i].get_fullname(), k, domains[j]));
            end

            if (k > 0) begin
               mems[i].read(status, k-1, val, vmm_ral::BFM, domains[j]);
               if (status != vmm_rw::IS_OK) begin
                  `vmm_error(log, $psprintf("Status was %s when reading \"%s[%0d]\" through domain \"%s\".",
                                            status.name(), mems[i].get_fullname(), k, domains[j]));
               end
               else begin
                  exp = ~(k-1) & ((1'b1<<n_bits)-1);
                  if (val !== exp) begin
                     `vmm_error(log, $psprintf("\"%s[%0d-1]\" read back as 'h%h instead of 'h%h.",
                                               mems[i].get_fullname(), k, val, exp));

                  end
               end

               mems[i].write(status, k-1, k-1, vmm_ral::BFM, domains[j]);
               if (status != vmm_rw::IS_OK) begin
                  `vmm_error(log, $psprintf("Status was %s when writing \"%s[%0d-1]\" through domain \"%s\".",
                                            status.name(), mems[i].get_fullname(), k, domains[j]));
               end
            end

            if (k == mems[i].get_size() - 1) begin
               mems[i].read(status, k, val, vmm_ral::BFM, domains[j]);
               if (status != vmm_rw::IS_OK) begin
                  `vmm_error(log, $psprintf("Status was %s when reading \"%s[%0d]\" through domain \"%s\".",
                                            status.name(), mems[i].get_fullname(), k, domains[j]));
               end
               else begin
                  exp = ~(k) & ((1'b1<<n_bits)-1);
                  if (val !== exp) begin
                     `vmm_error(log, $psprintf("\"%s[%0d]\" read back as 'h%h instead of 'h%h.",
                                               mems[i].get_fullname(), k, val, exp));

                  end
               end
            end
         end
      end
   end
endtask: mem_walk


task vmm_ral_tests::reg_access(vmm_ral_block blk,
                               vmm_log       log);
   vmm_ral_reg regs[];
   bit skip_reg = 0;

   if(blk == null)
   begin
     `vmm_error(log, $psprintf("vmm_ral_tests::reg_access - Null argument provided for vmm_ral_block"));
     return;
   end

   // Iterate over all registers, checking accesses
   blk.get_registers(regs);
   foreach (regs[i]) begin
      string domains[];

      // Registers with some attributes are not to be tested
      if (regs[i].get_attribute("NO_RAL_TESTS") != "" ||
	  regs[i].get_attribute("NO_REG_ACCESS_TEST") != "") continue;

      // Can only deal with registers with backdoor access
      if (regs[i].get_backdoor() == null) begin
         `vmm_warning(log, $psprintf("Register \"%s\" does not have a backdoor mechanism available",
                                     regs[i].get_fullname()));
         continue;
      end

      // Registers may be accessible from multiple physical interfaces (domains)
      regs[i].get_domains(domains);

      // Cannot test access if register contains RO or OTHER fields
      begin
         vmm_ral_field fields[];
         regs[i].get_fields(fields);
         foreach (fields[j]) begin
            foreach (domains[k]) begin
               if (fields[j].get_access(domains[k]) == vmm_ral::RO) begin
                  `vmm_warning(log, $psprintf("Register \"%s\" has RO bits",
                                              regs[i].get_fullname()));
                  skip_reg = 1; break;
               end
               if (fields[j].get_access(domains[k]) >= vmm_ral::OTHER) begin
                  `vmm_warning(log, $psprintf("Register \"%s\" has OTHER or USER bits",
                                              regs[i].get_fullname()));
                  skip_reg = 1; break;
               end
            end
            if (skip_reg == 1) break;
         end
         if (skip_reg == 1) begin
            skip_reg = 0;
            continue;
         end
      end

      // Access each register:
      // - Write complement of reset value via front door
      // - Read value via backdoor and compare against mirror
      // - Write reset value via backdoor
      // - Read via front door and compare against mirror
      foreach (domains[j]) begin
         vmm_rw::status_e status;
         bit [`VMM_RAL_DATA_WIDTH-1:0] v, exp;
      
         `vmm_note(log, $psprintf("Verifying access of register %s in domain \"%s\"...",
                                  regs[i].get_fullname(), domains[j]));

         v = regs[i].get();

         regs[i].write(status, ~v, vmm_ral::BFM, domains[j]);
         if (status != vmm_rw::IS_OK) begin
            `vmm_error(log, $psprintf("Status was %s when writing \"%s\" through domain \"%s\".",
                                      status.name(), regs[i].get_fullname(), domains[j]));
         end

         regs[i].mirror(status, vmm_ral::VERB, vmm_ral::BACKDOOR);
         if (status != vmm_rw::IS_OK) begin
            `vmm_error(log, $psprintf("Status was %s when reading reset value of register \"%s\" through backdoor.",
                                      status.name(), regs[i].get_fullname()));
         end

         regs[i].write(status, v, vmm_ral::BACKDOOR, domains[j]);
         if (status != vmm_rw::IS_OK) begin
            `vmm_error(log, $psprintf("Status was %s when writing \"%s\" through backdoor.",
                                      status.name(), regs[i].get_fullname()));
         end

         regs[i].mirror(status, vmm_ral::VERB, vmm_ral::BFM, domains[j]);
         if (status != vmm_rw::IS_OK) begin
            `vmm_error(log, $psprintf("Status was %s when reading reset value of register \"%s\" through domain \"%s\".",
                                      status.name(), regs[i].get_fullname(), domains[j]));
         end
      end
   end
endtask: reg_access


task vmm_ral_tests::mem_access(vmm_ral_block blk,
                               vmm_log       log);
   vmm_ral_mem mems[];

   if(blk == null)
   begin
     `vmm_error(log, $psprintf("vmm_ral_tests::mem_access - Null argument provided for vmm_ral_block"));
     return;
   end

   // Access each location in all memories
   blk.get_memories(mems);
   foreach (mems[i]) begin
      vmm_ral::access_e mode;
      string domains[];
      int n_bits;

      // Memories with some attributes are not to be tested
      if (mems[i].get_attribute("NO_RAL_TESTS") != "" ||
	  mems[i].get_attribute("NO_MEM_ACCESS_TEST") != "") continue;

      // Can only deal with memories with backdoor access
      if (mems[i].get_backdoor() == null) begin
         `vmm_warning(log, $psprintf("Memory \"%s\" does not have a backdoor mechanism available",
                                     mems[i].get_fullname()));
         continue;
      end

      n_bits = mems[i].get_n_bits();

      // Memories may be accessible from multiple physical interfaces (domains)
      mems[i].get_domains(domains);

      // Walk the memory via each domain
      foreach (domains[j]) begin
         vmm_rw::status_e status;
         bit [`VMM_RAL_DATA_WIDTH-1:0] val, exp, v;
      
         `vmm_note(log, $psprintf("Accessing memory %s in domain \"%s\"...\n",
                                  mems[i].get_fullname(), domains[j]));

         mode = mems[i].get_access(domains[j]);

         // The access process is, for address k:
         // - Write random value via front door
         // - Read via backdoor and expect same random value if RW
         // - Write complement of random value via back door
         // - Read via front door and expect inverted random value
         for (int k = 0; k < mems[i].get_size(); k++) begin
            val = $random & ((1'b1<<n_bits)-1);
            if (mode == vmm_ral::RO) begin
               mems[i].peek(status, k, exp);
               if (status != vmm_rw::IS_OK) begin
                  `vmm_error(log, $psprintf("Status was %s when reading \"%s[%0d]\" through backdoor.",
                                            status.name(), mems[i].get_fullname(), k));
               end
            end
            else exp = val;

            mems[i].write(status, k, val, vmm_ral::BFM, domains[j]);
            if (status != vmm_rw::IS_OK) begin
               `vmm_error(log, $psprintf("Status was %s when writing \"%s[%0d]\" through domain \"%s\".",
                                         status.name(), mems[i].get_fullname(), k, domains[j]));
            end

            val = 'x;
            mems[i].peek(status, k, val);
            if (status != vmm_rw::IS_OK) begin
               `vmm_error(log, $psprintf("Status was %s when reading \"%s[%0d]\" through backdoor.",
                                         status.name(), mems[i].get_fullname(), k));
            end
            else begin
               if (val !== exp) begin
                  `vmm_error(log, $psprintf("Backdoor \"%s[%0d]\" read back as 'h%h instead of 'h%h.",
                                            mems[i].get_fullname(), k, val, exp));
               end
            end

            exp = ~exp & ((1'b1<<n_bits)-1);
            mems[i].poke(status, k, exp);
            if (status != vmm_rw::IS_OK) begin
               `vmm_error(log, $psprintf("Status was %s when writing \"%s[%0d-1]\" through backdoor.",
                                         status.name(), mems[i].get_fullname(), k));
            end

            mems[i].read(status, k, val, vmm_ral::BFM, domains[j]);
            if (status != vmm_rw::IS_OK) begin
               `vmm_error(log, $psprintf("Status was %s when reading \"%s[%0d]\" through domain \"%s\".",
                                         status.name(), mems[i].get_fullname(), k, domains[j]));
            end
            else begin
               if (mode == vmm_ral::WO) begin
                  if (val !== '0) begin
                     `vmm_error(log, $psprintf("Front door \"%s[%0d]\" read back as 'h%h instead of 'h%h.",
                                               mems[i].get_fullname(), k, val, 0));
                  end
               end
               else begin
                  if (val !== exp) begin
                     `vmm_error(log, $psprintf("Front door \"%s[%0d]\" read back as 'h%h instead of 'h%h.",
                                               mems[i].get_fullname(), k, val, exp));
                  end
               end
            end
         end
      end
   end
endtask: mem_access


task vmm_ral_tests::shared_access(vmm_ral_block blk,
                                  vmm_log       log);
   vmm_ral_reg regs[];
   vmm_ral_mem mems[];

   if(blk == null)
   begin
     `vmm_error(log, $psprintf("vmm_ral_tests::shared_access - Null argument provided for vmm_ral_block"));
     return;
   end

   // Iterate over all registers, looking for shared registers
   blk.get_registers(regs);
   foreach (regs[i]) begin
      string domains[];
      vmm_ral_field fields[];
      bit [`VMM_RAL_DATA_WIDTH-1:0] other_mask;
      bit [`VMM_RAL_DATA_WIDTH-1:0] wo_mask[];

      // Registers with some attributes are not to be tested
      if (regs[i].get_attribute("NO_RAL_TESTS") != "" ||
	  regs[i].get_attribute("NO_SHARED_ACCESS_TEST") != "") continue;

      // Only look at shared registers
      if (regs[i].get_n_domains() < 2) continue;
      regs[i].get_domains(domains);

      // Let's see what kind of bits we have...
      regs[i].get_fields(fields);

      // Identify unpredictable bits and the ones we shouldn't change
      other_mask = 0;
      foreach (fields[k]) begin
         int lsb, w;

         lsb = fields[k].get_lsb_pos_in_register();
         w   = fields[k].get_n_bits();

         if (fields[k].get_access(domains[0]) >= vmm_ral::OTHER) begin
            repeat (w) begin
               other_mask[lsb++] = 1'b1;
            end
         end
      end

      // WO bits will always readback as 0's but the mirror
      // with return what is supposed to have been written
      // so we cannot use the mirror-check function
      wo_mask = new [domains.size()];
      foreach (domains[j]) begin
         bit [`VMM_RAL_DATA_WIDTH-1:0] wo;
         wo = 0;
         foreach (fields[k]) begin
            int lsb, w;

            lsb = fields[k].get_lsb_pos_in_register();
            w   = fields[k].get_n_bits();

            if (fields[k].get_access(domains[j]) == vmm_ral::WO) begin
               repeat (w) begin
                  wo[lsb++] = 1'b1;
               end
            end
         end
         wo_mask[j] = wo;
      end

      // Try to write through each domain
      foreach (domains[j]) begin
         vmm_rw::status_e status;
         bit [`VMM_RAL_DATA_WIDTH-1:0] prev, v;

         // The mirror should contain the initial value
         prev = regs[i].get();

         // Write a random value, except in those "don't touch" fields
         v = ({$random, $random} & ~other_mask) | (prev & other_mask);

         `vmm_note(log, $psprintf("Writing register %s via domain \"%s\"...",
                                  regs[i].get_fullname(), domains[j]));

         `vmm_debug(log, $psprintf("Writing 'h%h over 'h%h", v, prev));

         regs[i].write(status, v, vmm_ral::BFM, domains[j]);
         if (status != vmm_rw::IS_OK) begin
            `vmm_error(log, $psprintf("Status was %s when writing register \"%s\" through domain \"%s\".",
                                      status.name(), regs[i].get_fullname(), domains[j]));
         end

         foreach (domains[k]) begin
            bit [`VMM_RAL_DATA_WIDTH-1:0] actual, exp;

            `vmm_note(log, $psprintf("Reading register %s via domain \"%s\"...",
                                     regs[i].get_fullname(), domains[k]));

            // Was it what we expected?
            exp = regs[i].get() & ~wo_mask[k];

            regs[i].read(status, actual, vmm_ral::BFM, domains[k]);
            if (status != vmm_rw::IS_OK) begin
               `vmm_error(log, $psprintf("Status was %s when reading register \"%s\" through domain \"%s\".",
                                         status.name(), regs[i].get_fullname(), domains[k]));
            end

            `vmm_debug(log, $psprintf("Read 'h%h, expecting 'h%h",
                                      actual, exp));

            if (actual !== exp) begin
               `vmm_error(log, $psprintf("Register \"%s\" through domain \"%s\" is 'h%h instead of 'h%h after writing 'h%h via domain \"%s\" over 'h%h.",
                                         regs[i].get_fullname(), domains[k],
                                         actual, exp, v, domains[j], prev));
            end
         end
      end
   end
   
   // Iterate over all memories, looking for shared ones
   blk.get_memories(mems);
   foreach (mems[i]) begin
      string domains[];
      int read_from = -1;

      // Memories with some attributes are not to be tested
      if (mems[i].get_attribute("NO_RAL_TESTS") != "" ||
	  mems[i].get_attribute("NO_SHARED_ACCESS_TEST") != "") continue;

      // Only look at shared memories
      if (mems[i].get_n_domains() < 2) continue;
      mems[i].get_domains(domains);

      // We need at least a backdoor or a domain that can read
      // the shared memory
      if (mems[i].get_backdoor() == null) begin
         foreach (domains[j]) begin
            vmm_ral::access_e right;
            right = mems[i].get_access(domains[j]);
            if (right == vmm_ral::RW ||
                right == vmm_ral::RO) begin
               read_from = j;
               break;
            end
         end
         if (read_from < 0) begin
            `vmm_warning(mems[i].log, "Memory cannot be read from any domains or backdoor. Shared access not verified.");
            continue;
         end
      end

      // Try to write through each domain
      foreach (domains[j]) begin

         `vmm_note(log, $psprintf("Writing shared memory \"%s\" via domain \"%s\".",
                                  mems[i].get_fullname(), domains[j]));

         // All addresses
         for (int offset = 0; offset < mems[i].get_size(); offset++) begin
            vmm_rw::status_e status;
            bit [`VMM_RAL_DATA_WIDTH-1:0] prev, v;
            
            // Read the initial value
            if (mems[i].get_backdoor() != null) begin
               mems[i].peek(status, offset, prev);
               if (status != vmm_rw::IS_OK) begin
                  `vmm_error(log, $psprintf("Status was %s when reading initial value of \"%s\"[%0d] through backdoor.",
                                            status.name(), mems[i].get_fullname(), offset));
               end
            end
            else begin
               mems[i].read(status, offset, prev, vmm_ral::BFM, domains[read_from]);
               if (status != vmm_rw::IS_OK) begin
                  `vmm_error(log, $psprintf("Status was %s when reading initial value of \"%s\"[%0d] through domain \"%s\".",
                                            status.name(), mems[i].get_fullname(),
                                            offset, domains[read_from]));
               end
            end
            
            
            // Write a random value,
            v = {$random, $random};
            
            mems[i].write(status, offset, v, vmm_ral::BFM, domains[j]);
            if (status != vmm_rw::IS_OK) begin
               `vmm_error(log, $psprintf("Status was %s when writing \"%s\"[%0d] through domain \"%s\".",
                                         status.name(), mems[i].get_fullname(), offset, domains[j]));
            end
            
            // Read back from all other domains
            foreach (domains[k]) begin
               bit [`VMM_RAL_DATA_WIDTH-1:0] actual, exp;

               mems[i].read(status, offset, actual, vmm_ral::BFM, domains[k]);
               if (status != vmm_rw::IS_OK) begin
                  `vmm_error(log, $psprintf("Status was %s when reading %s[%0d] through domain \"%s\".",
                                         status.name(), mems[i].get_fullname(), offset, domains[k]));
               end

               // Was it what we expected?
               exp = v;
               if (mems[i].get_access(domains[j]) == vmm_ral::RO) begin
                  exp = prev;
               end
               if (mems[i].get_access(domains[k]) == vmm_ral::WO) begin
                  exp = 0;
               end
               // Trim to number of bits
               exp &= (1 << mems[i].get_n_bits()) - 1;
               if (actual !== exp) begin
                  `vmm_error(log, $psprintf("%s[%0d] through domain \"%s\" is 'h%h instead of 'h%h after writing 'h%h via domain \"%s\" over 'h%h.",
                                         mems[i].get_fullname(), offset, domains[k],
                                         actual, exp, v, domains[j], prev));
               end
            end
         end
      end
   end
endtask: shared_access
