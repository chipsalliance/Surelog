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


`ifndef VMM_RAL_TEST_PRE_INCLUDE
`define VMM_RAL_TEST_PRE_INCLUDE ral_env.svh
`endif

`include "vmm.sv"

`include `VMM_MACRO_TO_STRING(`VMM_RAL_TEST_PRE_INCLUDE)

program gen_html;

`ifdef VMM_RAL_TEST_POST_INCLUDE
`include `VMM_MACRO_TO_STRING(`VMM_RAL_TEST_POST_INCLUDE)
`endif

`ifndef RAL_TB_ENV
`define RAL_TB_ENV tb_env
`endif


vmm_log log = new("Documentation Generation", "HTML");
`RAL_TB_ENV env;


initial
begin
   vmm_ral_block_or_sys ral_model;
   string  fname;
   integer fp;

   env = new;

   ral_model = env.ral.get_model();
   if (ral_model == null) begin
      `vmm_fatal(log, "No RAL abstraction model was specified");
   end

   // Find out the name of the top-level block or system
   // And use it to create the HTML file
   fname = ral_model.get_name();
   fp = $fopen({fname, ".html"}, "w");
   if (!fp) begin
      int errno;
      string reason;
      errno = $ferror(fp, reason);
      `vmm_fatal(log, {"Cannot open ", fname, ".html for writing: ", reason});
   end

   // Generate the HTML header
   $fwrite(fp, {"<html><title>", fname, " RAL Model</title>\n"});
   $fwrite(fp, "<body>\n");

   // Is the top construct a block or a system?
   begin
      vmm_ral_block blk;
      vmm_ral_sys   sys;
      if (!$cast(blk, ral_model)) begin
         vmm_ral_sys   subsys[];
         string        domains[];
         vmm_ral_block blks[];

         // Must be a system!
         $cast(sys, ral_model);
         document_system(sys);

         // Document all subsystems in the top-level systems
         sys.get_all_subsys(subsys, domains);
         foreach(subsys[i]) begin
            document_system(subsys[i], domains[i]);
         end

         // Document all blocks in the design
         sys.get_all_blocks(blks, domains);
         foreach(blks[i]) begin
            document_block(blks[i], domains[i]);
         end
      end
      else begin
         document_block(blk);
      end
   end

   // We are done!
   $fwrite(fp, "</body></html>\n");
   $fclose(fp);

   `vmm_note(log, {"Documentation can be found in ", fname, ".html"});   
   env.report();
end


function void document_system(vmm_ral_sys sys,
                              string      domain = "");
   string name;

   name = sys.get_name();
   if (domain != "") begin
      name = {name, ".", domain};
   end
   $fwrite(fp, {"<h1>System ", name, "</h1>\n"});
endfunction: document_system


function void document_block(vmm_ral_block blk,
                             string        domain = "");
   string name;
   int n_cols;

   name = blk.get_name();
   if (domain != "") begin
      name = {name, ".", domain};
   end
   $fwrite(fp, {"<h1>Block ", name, "</h1>\n"});

   $fwrite(fp, "<h2>Registers</h2>\n");

   // One column in the table per bit in the physical interface
   n_cols = blk.get_n_bytes() * 8;

   begin
      vmm_ral_reg regs[];
      blk.get_registers(regs, domain);

      foreach(regs[i]) begin
         vmm_ral_field flds[];
         int last_col;

         last_col = n_cols;

         // Table header
         $fwrite(fp, "<table border=1 rules=all><tr><td colspan=%0d bgcolor=cyan><b>%s</b></td></tr><tr>\n",
                 n_cols, regs[i].get_name());

         regs[i].get_fields(flds);

         // Fields are returned right-to-left.
         // Must list them left-to-right
         for(int j = flds.size()-1; j >= 0; j--) begin
            int lsb, w;
            lsb = flds[j].get_lsb_pos_in_register();
            w = flds[j].get_n_bits();
            // Do we have blank bits on the left of the field?
            if (lsb+w < last_col) begin
               $fwrite(fp, "   <td colspan=%0d>&nbsp;</td>\n", last_col - (lsb+w));
            end

            $fwrite(fp, "   <td colspan=%0d halign=center>%s</td>\n", w, flds[j].get_name());
            
            last_col = lsb;
         end

         // Do we have blank LSB bits?
         if (last_col > 0) begin
            $fwrite(fp, "   <td colspan=%0d>&nbsp;</td>\n", last_col);
         end

         // Close table with index row
         $fwrite(fp, "</tr><tr halign=center>");
         for (int j = n_cols-1; j >= 0; j--) begin
            $fwrite(fp, "<td>%0d</td>", j);
         end
         $fwrite(fp, "</tr></table><br>&nbsp<br>\n");
      end
   end
endfunction: document_block


endprogram: gen_html

