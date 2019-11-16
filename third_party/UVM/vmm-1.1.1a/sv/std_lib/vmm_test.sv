// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    Copyright 2009 Mentor Graphics Corporation
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


class vmm_test_registry;
   static local vmm_opts _vmm_opts = init_opts();

   local static function vmm_opts init_opts();
     init_opts = _vmm_opts;
     if (init_opts == null) begin
       init_opts = new;
     end
     return init_opts;
   endfunction

   local static vmm_test registry[string];
   local static vmm_log log = new("vmm_test_registry", "class");
   local static int width = 1;

   extern `VMM_STATIC_M task run(vmm_env env);
   extern `VMM_STATIC_M function void list();

   extern /*local*/ `VMM_STATIC_M function void Xregister_testX(vmm_test tst);
   extern local `VMM_STATIC_M function void display_known_tests(ref string msg[$],
                                                                input bit fatal);
   function new();
      _vmm_opts = init_opts();
      void'(_vmm_opts.get_bit("test_help","List available testcases"));
      void'(_vmm_opts.get_string("test","Default","Name of testcase to run"));
   endfunction
endclass


function vmm_test::new(string name,
                       string doc = "");
   this.log = new("Testcase", name);
   this.doc = doc;
   this.registry.Xregister_testX(this);
endfunction


function void vmm_test::Xset_log_instanceX(string inst);
   this.log.set_instance(inst);
endfunction


function string vmm_test::get_name();
   return this.log.get_instance();
endfunction


function string vmm_test::get_doc();
   return this.doc;
endfunction


task vmm_test::run(vmm_env e);
   e.run();
endtask


function void vmm_test_registry::Xregister_testX(vmm_test tst);
   string name;

   if (tst == null) begin
      `vmm_error(log, "Attemtping to register NULL test.");
      return;
   end

   name = tst.get_name();

   if (registry.exists(name)) begin
      `vmm_error(log, `vmm_sformatf("Attempting to register test \"%s\" more than once.",
                                    name));
      return;
   end

   registry[name] = tst;

   if (name.len() > width) width = name.len();
endfunction


task vmm_test_registry::run(vmm_env env);
   string   testname;
   vmm_test tst = null;
   vmm_test one_tst = null;
  
   if (registry.num() == 1) begin
      void'(registry.first(testname));
      one_tst = registry[testname];
   end

   if (!registry.exists("Default")) begin
      // Create a default testcase and run it
      tst = new("Default", "Default testcase that simply calls env::run()");
   end

   if (_vmm_opts.get_bit("test_help", "List available testcases")) begin
      list();
      $finish();
   end

   testname = _vmm_opts.get_string("test", ,
                                   "Name of testcase to run");

   // If no tests were specified but only one test is known, run it
   if (testname == "") begin
      string str;

      // If there was only one user-defined tests, use it
      if (one_tst != null) begin
         tst = one_tst;
         testname = tst.get_name();
      end
      // If there is only the default test, use it
      else if (registry.num() == 1) begin
         void'(registry.first(testname));
         tst = registry[testname];
      end
      // Don't known which test to use!
      else begin
         string msg[$];

         msg.push_back("No test was selected at runtime using +vmm_test=<test>.");
         msg.push_back("Available tests are:");
         display_known_tests(msg, 1);
         return;
      end
   end
   else begin
      if (!registry.exists(testname)) begin
         string msg[$];
         string str;

         $sformat(str, "Unknown test name \"%s\" specified.", testname);
         msg.push_back(str);
         display_known_tests(msg, 1);
         return;
      end
      tst = registry[testname];
   end

   `vmm_note(log, `vmm_sformatf("Running test \"%s\"...", testname));
   tst.run(env);
endtask


function void vmm_test_registry::list();
   string msg[$];
   string str;

   msg.push_back("Available tests are:");
   msg.push_back(str);
   display_known_tests(msg, 0);
endfunction


function void vmm_test_registry::display_known_tests(ref string msg[$],
                                                     input bit fatal);
   bit [12:0] n = 0;
   string     str;
   static string spaces = "                                            ";

   n = 0;
   foreach (registry[name]) begin
      string testname = name;
      $sformat(str, "%d) %s%s : %s", n++, testname,
               spaces.substr(0, width-testname.len()-1),
               registry[name].get_doc());
      msg.push_back(str);
   end
   if ((fatal && log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV)) ||
       (!fatal && log.start_msg(vmm_log::NOTE_TYP, vmm_log::NORMAL_SEV))) begin
      foreach (msg[i]) void'(log.text(msg[i]));
      log.end_msg();
   end
endfunction
