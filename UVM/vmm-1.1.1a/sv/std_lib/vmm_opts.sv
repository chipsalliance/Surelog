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


class vmm_opts_info;
   typedef enum {NO_ARGS, STR_ARGS, INT_ARGS} arg_type_e;

   arg_type_e arg_type = NO_ARGS;
   string     opt;
   string     sarg;
   string     doc;
   string     fname;
   int        val;

   bit        opt_specified;
   bit        arg_specified;
   bit        expected;

   int line_num;
   static int width = 1;

   function new(string opt,
                string sarg = "");
      this.opt = opt;
      this.sarg = sarg;
      if (opt.len() > width) width = opt.len();
   endfunction

   function string help(bit [12:0] id);
      static string spaces = "                                          ";
      string fmt;
      string pad = spaces.substr(0, width-opt.len()-1);

      case (arg_type)
        NO_ARGS:  $sformat(fmt, "%d) %s%s       (%b) : %s",
                           id, opt, pad, (this.opt_specified) ? 1'b1 : 1'b0,
                           doc);
        STR_ARGS: $sformat(fmt, "%d) %s%s=<str> (%s) : %s",
                           id, opt, pad,
                           (this.opt_specified) ? this.sarg : "Unspec'd",
                           doc);
        INT_ARGS: $sformat(fmt, "%d) %s%s=<int> (%s) : %s",
                           id, opt, pad,
                           (this.opt_specified) ? this.sarg : "Unspec'd",
                           doc);
      endcase
      return fmt;
   endfunction
endclass


function bit vmm_opts::extract_opts_info();
   if (opts_extracted) return 1;
   opts_extracted = 1;

   // Option files first
   if ($test$plusargs("vmm_opts_file")) begin
      string format;
      if ($value$plusargs("vmm_opts_file+%s", format)) begin
         string opts_file[$];
         void'(split(format, opts_file));      
         foreach (opts_file[i]) begin
            parse_opts_file(opts_file[i]);
         end
      end
   end

   // Command-line overrides option file options
   if ($test$plusargs("vmm_opts+")) begin
      string format;
      if ($value$plusargs("vmm_opts+%s", format)) begin
         string opts[$];
         void'(split(format, opts));      
         foreach (opts[i]) begin
            add_specified_option(opts[i]);
         end
      end
   end
endfunction


function void vmm_opts::parse_opts_file(string filename);
   string t_str;
   int    fp;

   fp = $fopen(filename, "r"); 
   if (!fp) begin
      `vmm_fatal(log, `vmm_sformatf("Unable to open options file %s for reading", filename));
      return;
   end

   while ($fscanf(fp, "%s", t_str) == 1) begin
      string str;
      if (`vmm_str_match(t_str, "[+]")) begin
         str = `vmm_str_postmatch(t_str);
         add_specified_option(str, filename);
      end
   end
   $fclose(fp);
endfunction


function void vmm_opts::add_specified_option(string frmt,
                                             string fname = "Command Line");
   bit arg_specified;
   int val;
   int idx[$];
   string s_arg;
   string name;
   vmm_opts_info oinfo;

   arg_specified = 0;
   if (`vmm_str_match(frmt, "=")) begin
      s_arg = `vmm_str_postmatch(frmt);
      frmt = `vmm_str_prematch(frmt);
      arg_specified = 1;
   end

   if (opts_info.exists(frmt)) begin
      oinfo = opts_info[frmt];
      if (arg_specified) oinfo.sarg = s_arg;
   end
   else begin
      oinfo = new(frmt, s_arg);
      opts_info[frmt] = oinfo;
   end

   oinfo.opt_specified = 1;
   oinfo.arg_specified = arg_specified;
   oinfo.fname         = fname;
endfunction


function vmm_opts_info vmm_opts::get_opts_by_name(string name);
   string format;
   vmm_opts_info oinfo;
   int idx[$];
`ifdef INCA
   bit[8*120-1:0] vname;
   $swrite(vname, "vmm_%s",name);
`else
   string vname = {"vmm_", name};
`endif

   if (!opts_extracted)
      void'(extract_opts_info());

   if (opts_info.exists(name)) begin
      oinfo = opts_info[name];
   end
   else begin
      oinfo = new(name);
      opts_info[name] = oinfo;
   end

   if (!oinfo.expected && $test$plusargs(vname)) begin
      string sarg, format;
      oinfo.opt_specified = 1;
      format = `vmm_sformatf("vmm_%s=%%s", name);
      if ($value$plusargs(format, sarg)) begin
         oinfo.sarg = sarg;
         oinfo.arg_specified = 1;
      end
   end
   oinfo.expected = 1;

   return oinfo;
endfunction


function bit    vmm_opts::get_bit(string name,
                                  string doc = "");
   vmm_opts_info oinfo;

   oinfo = get_opts_by_name(name);
   oinfo.arg_type = vmm_opts_info::NO_ARGS;
   if (oinfo.doc == "") oinfo.doc = doc;
   if (oinfo.doc == "") begin
      `vmm_warning(log, `vmm_sformatf("No documentation specified for option \"%s\".",
                                      name));
   end
   return oinfo.opt_specified;
endfunction


function string vmm_opts::get_string(string name,
                                     string dflt = "",
                                     string doc = "");
   vmm_opts_info oinfo;

   oinfo = get_opts_by_name(name);
   oinfo.arg_type = vmm_opts_info::STR_ARGS;
   if (oinfo.doc == "") oinfo.doc = doc;
   if (oinfo.doc == "") begin
      `vmm_warning(log, `vmm_sformatf("No documentation specified for option \"%s\".",
                                      name));
   end
   if (oinfo.arg_specified) return oinfo.sarg;

   return dflt;
endfunction


function int    vmm_opts::get_int(string  name,
                                  int     dflt = 0,
                                  string  doc = "");
   vmm_opts_info oinfo;

   oinfo = get_opts_by_name(name);
   oinfo.arg_type = vmm_opts_info::INT_ARGS;
   if (oinfo.doc == "") oinfo.doc = doc;
   if (oinfo.doc == "") begin
      `vmm_warning(log, `vmm_sformatf("No documentation specified for option \"%s\".",
                                      name));
   end
   oinfo.val = oinfo.sarg.atoi();
   if (oinfo.arg_specified) return oinfo.val;

   return dflt;
endfunction


function void vmm_opts::get_help();
   string usage[$];
   vmm_opts_info unknown[$];
   int p;

   usage.push_back("VMM run-time options can be specified in the following formats:");
   usage.push_back("   1) +vmm_opts+<option1>+<option2>+<option3>+...");
   usage.push_back("   2) +vmm_<option1> +vmm_<option2> +vmm_<option3> ...");
   usage.push_back("   3) +<option1> +<option2> +<option3> ... in file(s)");
   usage.push_back("      specified using +vmm_opts_file+<fname1>+<fname2>+...");
   usage.push_back("   where <optionN> is <name>, <name>=<int> or <name>=<str>");
   usage.push_back(" ");
   usage.push_back("VMM run-time options defined by this simulation are:");
   foreach (opts_info[name]) begin
      vmm_opts_info opt = opts_info[name];
      if (opt.expected) usage.push_back(opt.help(++p));
      if (opt.opt_specified && !opt.expected) begin
         unknown.push_back(opt);
      end
   end
   if (log.start_msg(vmm_log::NOTE_TYP, vmm_log::NORMAL_SEV)) begin
      foreach (usage[i]) void'(log.text(usage[i]));
      log.end_msg();
   end

   if (unknown.size() > 0) begin
      string woops[$];
      woops.push_back("Following unknown VMM run-time options were specified:");
      foreach (unknown[i]) begin
         string txt, opt, fname;
         opt = unknown[i].opt; fname = unknown[i].fname;
         $sformat(txt, "   %0d) %s (specified via %s)", i, opt, fname);
         woops.push_back(txt);
      end
      if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::WARNING_SEV)) begin
         foreach (woops[i]) void'(log.text(woops[i]));
         log.end_msg();
      end
  end
endfunction


function bit vmm_opts::split(string line, output string argv[$]);
   string pre;
   string post;
   string tok[$];

   split = 1;
   
   if (line.len() == 0) return 0;
   post = line;
   forever begin
      if (`vmm_str_match(post, "[+]")) begin
         pre = `vmm_str_prematch(post);
         post = `vmm_str_postmatch(post);
         if (pre.len() != 0) begin
            // Only add the token if non-empty to strip leading blanks
            argv.push_back(pre);
         end
      end else begin
         //if no further matches, put in the last match if it's non-zero len
         if (post.len() > 0) begin
            argv.push_back(post);
         end
         break;
      end
   end
endfunction
