/******************************************************************************
 * (C) Copyright 2015 AMIQ Consulting
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * NAME:        svaunit_pkg.sv
 * PROJECT:     svaunit
 * Description: SVAUnit PACKAGE
 *******************************************************************************/


package svaunit_pkg;
   // UVM package
   import uvm_pkg::*;

// Defines UVM macros

// Define SVAUnit reporter
/* SLline 1 "../../../UVM/svaunit/sv/svaunit_reporter.svh" 1 */



class svaunit_reporter extends uvm_default_report_server;
   
  
   
   typedef uvm_object_registry#(svaunit_reporter,"svaunit_reporter") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     svaunit_reporter tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "svaunit_reporter"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     svaunit_reporter local_data__; /* Used for copy and compare */ 
     typedef svaunit_reporter ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 



      function new(string name = "svaunit_reporter");
      super.new(name);
   endfunction

   
   virtual function string compose_message(uvm_severity severity,
         string name,
         string id,
         string message,
         string filename,
         int line);

      uvm_severity_type severity_type = uvm_severity_type'(severity);

      if(severity_type == UVM_INFO) begin
         return $psprintf("%-8s @ %0t ns [%-7s]: %s", severity_type.name(), $time, id, message);
      end else begin
         return super.compose_message(severity, name, id, message, filename, line);
      end
   endfunction
endclass



/* SLline 33 "../../../UVM/svaunit/sv/svaunit_pkg.sv" 2 */

// Definitions of SVAUnit macros

// Definitions of SVAUnit versions macros

// Definitions of SVAUnit types
/* SLline 1 "../../../UVM/svaunit/sv/svaunit_types.svh" 1 */



typedef enum bit[1: 0] {SVAUNIT_FAIL = 0, SVAUNIT_PASS = 1, SVAUNIT_DID_NOT_RUN = 2} svaunit_status_type;

typedef enum bit {SVAUNIT_NOT_TESTED = 0, SVAUNIT_WAS_TESTED = 1} svaunit_sva_tested_type;

typedef enum int {
   SVAUNIT_IDLE = 0,
   SVAUNIT_START = 606,
   SVAUNIT_SUCCESS = 607,
   SVAUNIT_FAILURE = 608,
   SVAUNIT_STEP_SUCCESS = 609,
   SVAUNIT_STEP_FAILURE = 610,
   SVAUNIT_DISABLE = 611,
   SVAUNIT_ENABLE = 612,
   SVAUNIT_RESET = 613,
   SVAUNIT_KILL = 614
} svaunit_concurrent_assertion_state_type;


/* SLline 42 "../../../UVM/svaunit/sv/svaunit_pkg.sv" 2 */

// Definition of immediate assertion details
/* SLline 1 "../../../UVM/svaunit/sv/svaunit_concurrent_assertion_details.svh" 1 */



class svaunit_concurrent_assertion_details extends uvm_object;
   
  
   
   typedef uvm_object_registry#(svaunit_reporter,"svaunit_reporter") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     svaunit_reporter tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "svaunit_reporter"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     svaunit_reporter local_data__; /* Used for copy and compare */ 
     typedef svaunit_reporter ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 



      local time sva_end_time;

      svaunit_concurrent_assertion_state_type sva_state;

      local string test_name;

   
   function new(string name = "svaunit_concurrent_assertion_details");
      super.new(name);
   endfunction

   
   virtual function void create_new_detail(ref string a_test_name, svaunit_concurrent_assertion_state_type a_sva_state,
         time a_sva_time_end);

            sva_state = a_sva_state;
      set_sva_test_name(a_test_name);
      set_sva_end_time(a_sva_time_end);
   endfunction

   
   virtual function void set_sva_test_name(ref string a_test_name);
      test_name = a_test_name;
   endfunction

   
   virtual function void set_sva_end_time(time a_sva_end_time);
      sva_end_time = a_sva_end_time;
   endfunction

   
   virtual function time get_sva_end_time();
      return sva_end_time;
   endfunction

   
   virtual function svaunit_concurrent_assertion_state_type get_sva_state();
      return sva_state;
   endfunction

   
   virtual function bit sva_is_not_finished();
      return !sva_is_finished();
   endfunction

   
   virtual function bit sva_is_finished();
      if(sva_state == SVAUNIT_FAILURE || sva_state == SVAUNIT_SUCCESS)
         return 1;
      return 0;
   endfunction

   
   virtual function bit sva_failed();
            if(sva_state == SVAUNIT_FAILURE)
         return 1;
      return 0;
   endfunction

   
   virtual function bit sva_succeeded();
      if(sva_state == SVAUNIT_SUCCESS)
         return 1;
      return 0;
   endfunction


   
   virtual function string get_sva_details(ref string a_test_name);
            string states;

                              if(a_test_name == test_name)
         return $sformatf("state: %s, end time: %0d\n", sva_state.name(), sva_end_time);
      else
         return "";
   endfunction
endclass


/* SLline 45 "../../../UVM/svaunit/sv/svaunit_pkg.sv" 2 */

// Definition of immediate assertion info
/* SLline 1 "../../../UVM/svaunit/sv/svaunit_concurrent_assertion_info.svh" 1 */




class svaunit_concurrent_assertion_info extends uvm_object;
   
  
   
   typedef uvm_object_registry#(svaunit_reporter,"svaunit_reporter") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     svaunit_reporter tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "svaunit_reporter"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     svaunit_reporter local_data__; /* Used for copy and compare */ 
     typedef svaunit_reporter ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 



      local bit enable;

      local string sva_name;

      local string sva_path;

      local string sva_type;

      local svaunit_sva_tested_type tested;

      local svaunit_concurrent_assertion_details sva_details[$];

      local int nof_cover_failures;

      local int nof_cover_successfull;

      local string lof_tests_sva_enabled[$];

      local string lof_tests_sva_tested[$];

   
   function new(string name = "svaunit_concurrent_assertion_info");
      super.new(name);

            enable = 1;
   endfunction

   
   virtual function void create_new_sva(ref string a_sva_name, string a_sva_path, string a_sva_type);
            string test_name = "";
      svaunit_concurrent_assertion_state_type idle_state = SVAUNIT_IDLE;
      time current_time = $time();

      sva_name = a_sva_name;
      sva_type = a_sva_type;
      sva_path = a_sva_path;

            enable = 1;
      add_new_detail_sva(test_name, idle_state, current_time);
   endfunction

   
   virtual function void add_new_detail_sva(string a_test_name,
         svaunit_concurrent_assertion_state_type a_sva_state, time a_sva_end_time);

      svaunit_concurrent_assertion_details details;

      details = svaunit_concurrent_assertion_details::type_id::create(
         $sformatf("%s_detail_%s", sva_name, sva_details.size() - 1));
      
            sva_details.push_back(details);

            sva_details[sva_details.size() - 1].create_new_detail(a_test_name, a_sva_state, a_sva_end_time);
   endfunction

   
   virtual function int unsigned get_last_index_sva_finished();
            int unsigned last_index = 0;

            foreach(sva_details[index])
         if(sva_details[index].sva_state == SVAUNIT_FAILURE || sva_details[index].sva_state == SVAUNIT_SUCCESS)
            last_index = index;

            return last_index;
   endfunction

   
   virtual function svaunit_concurrent_assertion_state_type get_sva_state();
      return sva_details[sva_details.size() - 1].get_sva_state();
   endfunction

   
   virtual function bit sva_finished();
      if(sva_details.size() > 0)
         return (sva_details[$].sva_state == SVAUNIT_FAILURE || sva_details[$].sva_state == SVAUNIT_SUCCESS);
      else
         return 0;
   endfunction

   
   virtual function bit sva_not_finished();
      return !sva_finished();
   endfunction

   
   virtual function bit sva_passed();
      if(sva_details.size() > 0)
         return (sva_details[$].sva_state == SVAUNIT_SUCCESS);
      else
         return 0;
   endfunction

   
   virtual function bit sva_failed();
      if(sva_details.size() > 0)
         return (sva_details[$].sva_state == SVAUNIT_FAILURE);
      else
         return 0;
   endfunction

   
   virtual function void print_sva_array(string a_test_name);
      string text = "";
      for(int i = 0; i < sva_details.size(); i++)
         text = {text, $sformatf("%s ", sva_details[i].get_sva_details(a_test_name))};
      
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_INFO,get_name())) 
       uvm_report_info (get_name(), text, UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_concurrent_assertion_info.svh", 180, "", 1); 
   end
;
   endfunction


   
   virtual function int unsigned get_nof_times_sva_fails();
            int unsigned nof_times_sva_failed = 0;

      foreach(sva_details[index])
         if(sva_details[index].sva_state == SVAUNIT_FAILURE)
            nof_times_sva_failed = nof_times_sva_failed + 1;

            return nof_times_sva_failed;
   endfunction

   
   virtual function int unsigned get_nof_times_sva_succeeded();
            int unsigned nof_times_sva_succeeded = 0;

      foreach(sva_details[index])
         if(sva_details[index].sva_state == SVAUNIT_SUCCESS)
            nof_times_sva_succeeded = nof_times_sva_succeeded + 1;

            return nof_times_sva_succeeded;
   endfunction

   
   virtual function string get_sva_name();
      return sva_name;
   endfunction

   
   virtual function string get_sva_path();
      return sva_path;
   endfunction

   
   virtual function string get_sva_type();
      return sva_type;
   endfunction

   
   virtual function void set_enable(ref string a_test_name, bit a_enable_bit);
      enable = a_enable_bit;

      if(a_enable_bit) begin
         lof_tests_sva_enabled.push_back(a_test_name);
      end
   endfunction

   
   virtual function bit sva_enabled(string a_test_name);
      print_sva_array(a_test_name);

      if(get_sva_type() != "vpiCover") begin
         foreach(lof_tests_sva_enabled[test_index]) begin
            if(lof_tests_sva_enabled[test_index] == a_test_name) begin
               return enable;
            end
         end
      end else begin
         return enable;
      end

      return 0;
   endfunction

   virtual function bit sva_disabled(string a_test_name);
      return !sva_enabled(a_test_name);
   endfunction

   
   virtual function bit was_enable(string a_test_name);
      foreach(lof_tests_sva_enabled[test_index]) begin
         if(lof_tests_sva_enabled[test_index] == a_test_name) begin
            return 1;
         end
      end

      return 0;
   endfunction

   
   virtual function void set_tested(string a_test_name);
      tested = SVAUNIT_WAS_TESTED;

      lof_tests_sva_tested.push_back(a_test_name);
   endfunction

   
   virtual function svaunit_sva_tested_type was_tested(string a_test_name);
      if(lof_tests_sva_tested.size() > 0) begin
         foreach(lof_tests_sva_tested[test_index]) begin
            if(lof_tests_sva_tested[test_index] == a_test_name) begin
               return tested;
            end
         end
      end

      return SVAUNIT_NOT_TESTED;
   endfunction

   
   virtual function void set_nof_attempts_failed_covered(int a_nof_attempts_failed);
                  if(a_nof_attempts_failed == (-1)) begin
         nof_cover_failures = 0;
      end else begin
         nof_cover_failures = a_nof_attempts_failed;
      end
   endfunction

   
   virtual function int unsigned get_nof_attempts_failed_covered();
      return nof_cover_failures;
   endfunction

   
   virtual function void set_nof_attempts_successfull_covered(int a_nof_attempts_successfull);
                  if(a_nof_attempts_successfull == (-1)) begin
         nof_cover_successfull = 0;
      end else begin
         nof_cover_successfull = a_nof_attempts_successfull;
      end
   endfunction

   
   virtual function int unsigned get_nof_attempts_successful_covered();
      return nof_cover_successfull;
   endfunction

   
   virtual function void print_sva_info(string a_test_name);
            string details;

                                    
      
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_INFO,get_name())) 
       uvm_report_info (get_name(), text, UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_concurrent_assertion_info.svh", 364, "", 1); 
   end

      
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_INFO,get_name())) 
       uvm_report_info (get_name(), text, UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_concurrent_assertion_info.svh", 365, "", 1); 
   end


      foreach(sva_details[index]) begin
         details = sva_details[index].get_sva_details(a_test_name);
         if(details != "") begin
            
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_INFO,get_name())) 
       uvm_report_info (get_name(), text, UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_concurrent_assertion_info.svh", 370, "", 1); 
   end

         end
      end
   endfunction
endclass


/* SLline 48 "../../../UVM/svaunit/sv/svaunit_pkg.sv" 2 */

// Definition of SVA details
/* SLline 1 "../../../UVM/svaunit/sv/svaunit_immediate_assertion_details.svh" 1 */



class svaunit_immediate_assertion_details extends uvm_object;
   
  
   
   typedef uvm_object_registry#(svaunit_reporter,"svaunit_reporter") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     svaunit_reporter tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "svaunit_reporter"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     svaunit_reporter local_data__; /* Used for copy and compare */ 
     typedef svaunit_reporter ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 



      string check_name;

      time attempt_time[$];

      svaunit_status_type check_states[$];

      string tests_names[$];

   
   function new(input string name = "svaunit_immediate_assertion_details");
      super.new(name);
   endfunction

   
   virtual function void set_check_name(ref string a_check_name);
      check_name = a_check_name;
   endfunction

   
   virtual function string get_check_name();
      return check_name;
   endfunction

   
   virtual function void add_test_name(ref string a_test_name);
      tests_names.push_back(a_test_name);
   endfunction

   
   virtual function void add_test_time(time a_test_time);
      attempt_time.push_back(a_test_time);
   endfunction

   
   virtual function void add_status(svaunit_status_type a_status);
      check_states.push_back(a_status);
   endfunction

   
   virtual function void create_new_check_detail(string a_check_name, string a_test_name, time a_test_time,
         svaunit_status_type a_status);
      set_check_name(a_check_name);
      add_test_name(a_test_name);
      add_test_time(a_test_time);
      add_status(a_status);
   endfunction

   
   virtual function void add_new_detail(string a_test_name, time a_test_time, svaunit_status_type a_status);
      add_test_name(a_test_name);
      add_test_time(a_test_time);
      add_status(a_status);
   endfunction

   
   virtual function int unsigned get_nof_times_check_has_passed();
            int unsigned nof_tests_passed = 0;

            foreach(check_states[status_index]) begin
         if(check_states[status_index] == SVAUNIT_PASS) begin
            nof_tests_passed = nof_tests_passed + 1;
         end
      end

            return nof_tests_passed;
   endfunction

   
   virtual function int unsigned get_nof_times_check_was_tested();
      return check_states.size();
   endfunction

   
   virtual function string get_check_attempts();
      string star = " ";

      if(get_nof_times_check_has_passed() < get_nof_times_check_was_tested()) begin
         star = "*";
      end

      return $sformatf("%s   %s %0d/%0d PASSED", star, check_name, get_nof_times_check_has_passed(),
         get_nof_times_check_was_tested());
   endfunction

      function svaunit_immediate_assertion_details copy();
      copy = svaunit_immediate_assertion_details::type_id::create("copy_svaunit_immediate_assertion_details");

      copy.check_name = check_name;

      foreach(tests_names[index]) begin
         copy.tests_names.push_back(tests_names[index]);
      end

      foreach(attempt_time[index]) begin
         copy.attempt_time.push_back(attempt_time[index]);
      end

      foreach(check_states[index]) begin
         copy.check_states.push_back(check_states[index]);
      end

      return copy;
   endfunction
endclass


/* SLline 51 "../../../UVM/svaunit/sv/svaunit_pkg.sv" 2 */

// Definition of SVA info
/* SLline 1 "../../../UVM/svaunit/sv/svaunit_immediate_assertion_info.svh" 1 */



class svaunit_immediate_assertion_info extends uvm_object;
   
  
   
   typedef uvm_object_registry#(svaunit_reporter,"svaunit_reporter") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     svaunit_reporter tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "svaunit_reporter"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     svaunit_reporter local_data__; /* Used for copy and compare */ 
     typedef svaunit_reporter ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 



      svaunit_concurrent_assertion_info sva_tested;

      svaunit_immediate_assertion_details checks_details[];

   
   function new(input string name = "svaunit_immediate_assertion_info");
      super.new(name);
   endfunction

   
   virtual function svaunit_concurrent_assertion_info get_sva_tested();
      return sva_tested;
   endfunction

   
   virtual function bit check_exists(string a_check_name);
                  int check_index[$];

      check_index = checks_details.find_index() with (item.get_check_name() == a_check_name);

      if(check_index.size() > 0) begin
         return 1;
      end else begin
         return 0;
      end
   endfunction

   
   virtual function void add_new_check_detail(string a_check_name, string a_test_name, time a_time,
         svaunit_status_type a_status);

                  int check_index[$];

      check_index = checks_details.find_index() with (item.get_check_name() == a_check_name);
      
      if(check_index.size() > 0) begin
         foreach(check_index[index]) begin
            checks_details[check_index[index]].add_new_detail(a_test_name, a_time, a_status);
         end
      end else begin
                  checks_details = new[checks_details.size() + 1](checks_details);
         checks_details[checks_details.size() - 1] = svaunit_immediate_assertion_details::type_id::create(
            $sformatf("%s_detail_%s", a_check_name, checks_details.size() - 1));
         checks_details[checks_details.size() - 1].create_new_check_detail(a_check_name, a_test_name, a_time, a_status);
      end
   endfunction

   
   virtual function void set_sva(svaunit_concurrent_assertion_info a_sva);
      sva_tested = a_sva;
   endfunction

   
   virtual function int unsigned get_nof_times_sva_has_failed();
            int unsigned nof_times_assertion_failed = 0;

            foreach(checks_details[details_index]) begin
         nof_times_assertion_failed = nof_times_assertion_failed +
         (checks_details[details_index].get_nof_times_check_was_tested()
            - checks_details[details_index].get_nof_times_check_has_passed());
      end

            return nof_times_assertion_failed;
   endfunction

   
   virtual function int unsigned get_nof_times_sva_was_tested();
            int unsigned nof_times_assertion_tested = 0;

            foreach(checks_details[details_index]) begin
         nof_times_assertion_tested = nof_times_assertion_tested +
         checks_details[details_index].get_nof_times_check_was_tested();
      end

            return nof_times_assertion_tested;
   endfunction

   
   virtual function string get_checks_for_sva();
            string details = "";
      string star = "";
      int unsigned nof_times_sva_tested = get_nof_times_sva_was_tested();
      int unsigned nof_times_sva_failed = get_nof_times_sva_has_failed();

      if(nof_times_sva_failed > 0) begin
         star = "*";
      end

      if(sva_tested != null) begin
         details = $sformatf("%s   %s   %0d/%0d checks PASSED", star, sva_tested.get_sva_name(), nof_times_sva_tested -
            nof_times_sva_failed, nof_times_sva_tested);
      end else begin
         details = $sformatf("%s   %0d/%0d checks PASSED", star, nof_times_sva_tested - nof_times_sva_failed,
            nof_times_sva_tested);
      end

      checks_details.rsort(item) with (item.get_nof_times_check_has_passed() < item.get_nof_times_check_was_tested());

            foreach(checks_details[details_index]) begin
         details = $sformatf("%s\n\t\t%s", details, checks_details[details_index].get_check_attempts());
      end

      details = $sformatf("%s\n", details);

            return details;
   endfunction

   
   virtual function string get_sva_failed_details();
            string details = "";
      string star = "";
      int unsigned nof_times_sva_failed = get_nof_times_sva_has_failed();

      if(nof_times_sva_failed > 0) begin
         star = "*";
         details = $sformatf("%s\t%s   %s", details, star, sva_tested.get_sva_name());
      end

            return details;
   endfunction

   
   virtual function bit details_exists(string a_check_name, ref string a_lof_checks[$]);
                  int check_index[$];

      check_index = a_lof_checks.find_index() with (item == a_check_name);

      if(check_index.size() > 0) begin
         return 1;
      end else begin
         return 0;
      end
   endfunction

   
   virtual function void get_checks_names(ref string a_lof_used_checks[$]);
      foreach(checks_details[details_index]) begin
         if(!details_exists(checks_details[details_index].get_check_name(), a_lof_used_checks)) begin
            a_lof_used_checks.push_back(checks_details[details_index].get_check_name());
         end
      end
   endfunction

   
   virtual function svaunit_immediate_assertion_info get_checks(string a_test_name);
            int check_index[$];

            bit was_tested = 0;

      get_checks = copy();
      get_checks.checks_details.delete();

      foreach(checks_details[details_index]) begin
         check_index = checks_details[details_index].tests_names.find_index() with (item == a_test_name);

         foreach(check_index[index]) begin
            was_tested = 1;
            get_checks.add_new_check_detail(
               checks_details[details_index].get_check_name(),
               a_test_name,
               checks_details[details_index].attempt_time[check_index[index]],
               checks_details[details_index].check_states[check_index[index]]);
         end
      end

      if(was_tested == 0) begin
         get_checks = null;
      end

      return get_checks;
   endfunction

      virtual function void print_checks();
            string tested = "";

      
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_INFO,get_name())) 
       uvm_report_info (get_name(), text, UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_immediate_assertion_info.svh", 257, "", 1); 
   end


      foreach(checks_details[index]) begin
         tested = $sformatf("%s\n %s", tested, checks_details[index].get_check_attempts());
      end

      
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_INFO,get_name())) 
       uvm_report_info (get_name(), text, UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_immediate_assertion_info.svh", 263, "", 1); 
   end

   endfunction

      function svaunit_immediate_assertion_info copy();
      copy = svaunit_immediate_assertion_info::type_id::create("copy_svaunit_immediate_assertion_info");
      
      copy.sva_tested = sva_tested;

      foreach(checks_details[index]) begin
         copy.checks_details = new[copy.checks_details.size() + 1](copy.checks_details);
         copy.checks_details[copy.checks_details.size() - 1] = svaunit_immediate_assertion_details::type_id::create(
            $sformatf("%s_copy_detail_%s", checks_details[index].get_check_name(), copy.checks_details.size() - 1));
         copy.checks_details[copy.checks_details.size() - 1] = checks_details[index].copy();
      end

      return copy;
   endfunction
endclass


/* SLline 54 "../../../UVM/svaunit/sv/svaunit_pkg.sv" 2 */

// Definition of SVAUnit VPI wrapper class
/* SLline 1 "../../../UVM/svaunit/sv/svaunit_vpi_wrapper.svh" 1 */



class svaunit_vpi_wrapper extends uvm_object;

      virtual svaunit_vpi_interface vpi_vif;

      local string test_name;

      
  
   
   typedef uvm_object_registry#(svaunit_reporter,"svaunit_reporter") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     svaunit_reporter tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "svaunit_reporter"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     svaunit_reporter local_data__; /* Used for copy and compare */ 
     typedef svaunit_reporter ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 



      local const string LOF_ALL_SVAUNIT_CHECKS[9];

      local svaunit_immediate_assertion_info lof_checks[$];

      bit stop_test;

      svaunit_status_type current_check_status;

   
   function new(string name = "svaunit_vpi_wrapper");
      super.new(name);

            if (!uvm_config_db#(virtual svaunit_vpi_interface)::get(uvm_root::get(), "*", "VPI_VIF", vpi_vif)) begin
         
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_FATAL,"SVAUNIT_VPI_WRAPPER_NO_VIF_ERR")) 
       uvm_report_fatal ("SVAUNIT_VPI_WRAPPER_NO_VIF_ERR", 
            "SVAUnit VPI interface for vpi_wrapper class is not set! Please enable SVAUnit package!", UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_vpi_wrapper.svh", 56, "", 1); 
   end

      end

      LOF_ALL_SVAUNIT_CHECKS = '{
         "CHECK_SVA_EXISTS",
         "CHECK_SVA_ENABLED",
         "CHECK_SVA_DISABLED",
         "CHECK_SVA_PASSED",
         "CHECK_SVA_FAILED",
         "CHECK_SVA_FINISHED",
         "CHECK_SVA_NOT_FINISHED",
         "CHECK_ALL_SVA_PASSED",
         "CHECK_THAT"
      };

      current_check_status = SVAUNIT_DID_NOT_RUN;
   endfunction

      virtual function void update_coverage();
            vpi_vif.update_coverage(test_name);
   endfunction

   
   virtual function string get_test_name();
      return test_name;
   endfunction

   
   virtual function void set_test_name_vpi(string a_test_name);
      test_name = a_test_name;

      vpi_vif.set_test_name(a_test_name);
   endfunction

   
   
   local function void add_check(svaunit_concurrent_assertion_info a_sva, string a_check_name,
         time a_time, svaunit_status_type a_status);

            int check_index[$];

            check_index = lof_checks.find_index() with (item.get_sva_tested() == a_sva);

      if(check_index.size() > 0) begin
         foreach(check_index[index]) begin
            lof_checks[check_index[index]].add_new_check_detail(a_check_name, test_name, a_time, a_status);
         end
      end else begin
         svaunit_immediate_assertion_info check = svaunit_immediate_assertion_info::type_id::create($sformatf(
               "%s_immediate_assertions_%0d", get_name(), lof_checks.size() - 1));
         check.set_sva(a_sva);
         check.add_new_check_detail(a_check_name, test_name, a_time, a_status);

         lof_checks.push_back(check);
      end
   endfunction

   
   virtual function svaunit_immediate_assertion_info get_check_for_sva(string a_sva_name);
      svaunit_immediate_assertion_info checks[$];

      checks = lof_checks.find_first() with (item.sva_tested.get_sva_name() == a_sva_name);

      return checks[0];
   endfunction

   
   virtual function void get_checks_for_test(string a_test_name,
         ref svaunit_immediate_assertion_info a_checks_for_test[$]);

      foreach(lof_checks[check_index]) begin
         svaunit_immediate_assertion_info check = lof_checks[check_index].get_checks(a_test_name);

         if(check != null) begin
            int test_check_index[$];

            if(lof_checks[check_index].sva_tested != null) begin
               test_check_index = a_checks_for_test.find_index()
               with (item.sva_tested.get_sva_name() == check.sva_tested.get_sva_name());

               if(test_check_index.size() > 0) begin
                  foreach(test_check_index[index]) begin
                     foreach(check.checks_details[details_index]) begin
                                                for(int time_idx = 0;
                              time_idx < check.checks_details[details_index].attempt_time.size(); time_idx++) begin
                           a_checks_for_test[test_check_index[index]].add_new_check_detail(
                              check.checks_details[details_index].get_check_name(),
                              a_test_name,
                              check.checks_details[details_index].attempt_time[time_idx],
                              check.checks_details[details_index].check_states[time_idx]);
                        end
                     end
                  end
               end else begin
                  a_checks_for_test.push_back(check);
               end
            end
         end
      end
   endfunction

   
   virtual function void get_checks_names(ref svaunit_immediate_assertion_info a_lof_used_checks[$],
         ref string a_lof_used_checks_names[$]);
      foreach(a_lof_used_checks[check_index]) begin
         foreach(a_lof_used_checks[check_index].checks_details[detail_index]) begin
            int indexes[$];

            indexes =  a_lof_used_checks_names.find_index() with (
                  a_lof_used_checks[check_index].checks_details[detail_index].get_check_name() == item);

            if(indexes.size() == 0) begin
               a_lof_used_checks_names.push_back(
                  a_lof_used_checks[check_index].checks_details[detail_index].get_check_name());
            end
         end
      end
   endfunction

   
   virtual function void get_checks_not_used_names(ref svaunit_immediate_assertion_info a_lof_used_checks[$],
         ref string a_lof_not_used_checks_names[$]);
            int check_index[$];

            int string_index[$];

            foreach(LOF_ALL_SVAUNIT_CHECKS[name_index]) begin

                  check_index = a_lof_used_checks.find_index() with (item.check_exists(LOF_ALL_SVAUNIT_CHECKS[name_index]));

                  if(check_index.size() == 0) begin
                        string_index = a_lof_not_used_checks_names.find_index() with (item == LOF_ALL_SVAUNIT_CHECKS[name_index]);

                        if(string_index.size() == 0) begin
               a_lof_not_used_checks_names.push_back(LOF_ALL_SVAUNIT_CHECKS[name_index]);
            end
         end
      end
   endfunction

   
   virtual function int unsigned get_total_nof_checks();
      return lof_checks.size();
   endfunction

   
   virtual function int unsigned get_nof_times_check_was_tested(string a_check_name,
         ref svaunit_immediate_assertion_info a_lof_used_checks[$]);
            int unsigned nof_times_check_was_tested = 0;

                  foreach(a_lof_used_checks[check_index]) begin
         foreach(a_lof_used_checks[check_index].checks_details[details_index])begin
            if(a_lof_used_checks[check_index].checks_details[details_index].get_check_name() == a_check_name) begin
               nof_times_check_was_tested = nof_times_check_was_tested +
               a_lof_used_checks[check_index].checks_details[details_index].get_nof_times_check_was_tested();
            end
         end
      end

      return nof_times_check_was_tested;
   endfunction

   
   virtual function int unsigned get_nof_times_check_has_passed(string a_check_name,
         ref svaunit_immediate_assertion_info a_lof_used_checks[$]);
            int unsigned nof_times_check_has_passed = 0;

                  foreach(a_lof_used_checks[check_index]) begin
         foreach(a_lof_used_checks[check_index].checks_details[details_index])begin
            if(a_lof_used_checks[check_index].checks_details[details_index].get_check_name() == a_check_name) begin
               nof_times_check_has_passed = nof_times_check_has_passed +
               a_lof_used_checks[check_index].checks_details[details_index].get_nof_times_check_has_passed();
            end
         end
      end

      return nof_times_check_has_passed;
   endfunction
   
   
   
   local function svaunit_concurrent_assertion_info get_assertion_by_path(string a_sva_path);
            svaunit_concurrent_assertion_info assertion = vpi_vif.get_assertion_from_path(a_sva_path);

            check_sva_exists(a_sva_path, $sformatf("Assertion %s doesn't exist.", a_sva_path));

      return assertion;
   endfunction

   
   local function svaunit_concurrent_assertion_info get_assertion_by_name(string a_sva_name);
            svaunit_concurrent_assertion_info assertion = vpi_vif.get_assertion_by_name(a_sva_name);

            check_sva_exists(a_sva_name, $sformatf("Assertion %s doesn't exist.", a_sva_name));

      return assertion;
   endfunction

   
   virtual function svaunit_concurrent_assertion_info get_assertion(string a_sva);
      if(is_a_path(a_sva)) begin
         return get_assertion_by_path(a_sva);
      end else begin
         return get_assertion_by_name(a_sva);
      end
   endfunction


   
   virtual function bit assertion_succeeded(string a_sva_name);
            svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         return assertion.sva_passed();
      end else begin
         return 0;
      end
   endfunction


   
   virtual function svaunit_concurrent_assertion_state_type get_state(string a_sva_name);
            svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         return assertion.get_sva_state();
      end else begin
         return svaunit_concurrent_assertion_state_type'(0);
      end
   endfunction

   
   virtual function bit is_finished(string a_sva_name);
            svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         return assertion.sva_finished();
      end else begin
         return 0;
      end
   endfunction

   
   virtual function bit is_not_finished(string a_sva_name);
            svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         return assertion.sva_not_finished();
      end else begin
         return 0;
      end
   endfunction

   
   virtual function bit is_enable(string a_sva_name);
            svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         return assertion.sva_enabled(get_test_name());
      end else begin
         return 0;
      end
   endfunction

   
   virtual function int get_nof_times_assertion_failed(string a_sva_name);
            svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         return assertion.get_nof_times_sva_fails();
      end else begin
         return -1;
      end
   endfunction

   
   virtual function int get_nof_times_assertion_succeeded(string a_sva_name);
            svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         return assertion.get_nof_times_sva_succeeded();
      end else begin
         return -1;
      end
   endfunction

   
   virtual function void get_sva_tested(string a_test_name, ref svaunit_concurrent_assertion_info a_sva_tested[$]);
      foreach(vpi_vif.sva_info[index]) begin
         if(vpi_vif.sva_info[index].was_tested(a_test_name) == SVAUNIT_WAS_TESTED) begin
            if(!vpi_vif.sva_exists(vpi_vif.sva_info[index].get_sva_name(),
                     vpi_vif.sva_info[index].get_sva_path(), a_sva_tested)) begin
               a_sva_tested.push_back(vpi_vif.sva_info[index]);
            end
         end
      end
   endfunction

      virtual function int unsigned get_nof_sva();
      return vpi_vif.get_nof_sva();
   endfunction

   
   virtual function int unsigned get_nof_tested_sva(string a_test_name);
            svaunit_concurrent_assertion_info tested_sva[$];

            get_sva_tested(a_test_name, tested_sva);

      return tested_sva.size();
   endfunction

   
   virtual function void get_sva_tested_names(ref svaunit_concurrent_assertion_info a_tested_sva[$],
         string a_tested_sva_names[$]);

      foreach(a_tested_sva[index]) begin
                  int tested_sva_index[$];

                  tested_sva_index = a_tested_sva_names.find_index() with (item == a_tested_sva[index].get_sva_path());

                  if(tested_sva_index.size() == 0) begin
            a_tested_sva_names.push_back(a_tested_sva[index].get_sva_path());
         end
      end
   endfunction

   
   virtual function void get_sva_not_tested_names(ref svaunit_concurrent_assertion_info a_not_tested_sva[$],
         string a_not_tested_sva_names[$]);

            foreach(a_not_tested_sva[index]) begin
                  int not_tested_index[$];

                  not_tested_index = a_not_tested_sva_names.find_index() with (item == a_not_tested_sva[index].get_sva_path());

                  if(not_tested_index.size() == 0) begin
            a_not_tested_sva_names.push_back(a_not_tested_sva[index].get_sva_path());
         end
      end
   endfunction

   
   virtual function void get_sva_not_tested(string a_test_name,
         ref svaunit_concurrent_assertion_info a_sva_not_tested[$]);

            svaunit_concurrent_assertion_info sva_tested[$];

            get_sva_tested(a_test_name, sva_tested);

            foreach(vpi_vif.sva_info[index]) begin
                  int not_tested_index[$];

                  not_tested_index = sva_tested.find_index() with (item == vpi_vif.sva_info[index]);

                  if(not_tested_index.size() == 0) begin
            a_sva_not_tested.push_back(vpi_vif.sva_info[index]);
         end
      end
   endfunction
   

   
      
   virtual function void reset_assertion(string a_sva_name);
            svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         vpi_vif.reset_assertion(get_test_name(), assertion);
      end
   endfunction

      virtual function void reset_all_assertions();
      vpi_vif.reset_all_assertions(get_test_name());
   endfunction

      
   virtual function void disable_assertion(string a_sva_name);
            svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         vpi_vif.disable_assertion(get_test_name(), assertion);
      end
   endfunction

   
   virtual function void disable_all_assertions();
      vpi_vif.disable_all_assertions(get_test_name());
   endfunction

      
   virtual function void enable_assertion(string a_sva_name);
            svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         vpi_vif.enable_assertion(get_test_name(), assertion);
      end
   endfunction

   
   virtual function void enable_all_assertions();
      vpi_vif.enable_all_assertions(get_test_name());
   endfunction

      
   virtual function void kill_assertion(string a_sva_name, time a_sim_time);
            svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         vpi_vif.kill_assertion(get_test_name(), assertion, a_sim_time);
      end
   endfunction

   
   virtual function void kill_all_assertions(time a_sim_time);
      vpi_vif.kill_all_assertions(get_test_name(), a_sim_time);
   endfunction

      
   virtual function void disable_step_assertion(string a_sva_name);
            svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         vpi_vif.disable_step_assertion(get_test_name(), assertion);
      end
   endfunction

   
   virtual function void disable_step_all_assertions();
      vpi_vif.disable_step_all_assertions(get_test_name());
   endfunction

   
   
   virtual function void enable_step_assertion(string a_sva_name);
            svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         vpi_vif.enable_step_assertion(get_test_name(), assertion);
      end
   endfunction

   
   virtual function void enable_step_all_assertions();
      vpi_vif.enable_step_all_assertions(get_test_name());
   endfunction

      
   virtual function void system_reset_all_assertions();
      vpi_vif.system_reset_all_assertions();
   endfunction

         virtual function void system_on_all_assertions();
      vpi_vif.system_on_all_assertions(get_test_name());
   endfunction

         virtual function void system_off_all_assertions();
      vpi_vif.system_off_all_assertions(get_test_name());
   endfunction

      
   virtual function void system_end_all_assertions();
      vpi_vif.system_end_all_assertions(get_test_name());
   endfunction
   
   
   
   virtual function int find(string a_s1, string a_s2);
      if(a_s1.len() < a_s2.len()) begin
         return -1;
      end else begin
         for(int char_index = 0; char_index < a_s1.len(); char_index = char_index + 1) begin
            if(a_s1.substr(char_index, char_index + a_s2.len() - 1) == a_s2) begin
               return char_index;
            end
         end
      end

      return -1;
   endfunction

   
   local function bit is_a_path(string a_sva_name);
      if(find(a_sva_name, ".") != -1) begin
                  return 1;
      end else begin
                  return 0;
      end
   endfunction

   
   local function bit check_expression(bit a_expression);
                  if (a_expression) begin
         current_check_status = SVAUNIT_PASS;
         return 1;
      end else begin
         stop_test = 1;
         current_check_status = SVAUNIT_FAIL;
         return 0;
      end
   endfunction

   
   local function svaunit_status_type get_current_check_status();
      return current_check_status;
   endfunction

   
   local task check_assertion_is_enabled(string a_sva_name);
      vpi_vif.wait_for_eots();
      vpi_vif.get_info_from_c(get_test_name());
      check_sva_enabled(a_sva_name, $sformatf("Assertion %s is not enabled", a_sva_name));
   endtask

      
   virtual function void check_sva_enabled(string a_sva_name, string a_error_msg = "The SVA should have been enabled.",
         int unsigned a_line = 0, string a_filename = "");

            svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         CHECK_SVA_ENABLED : assert(check_expression(assertion.sva_enabled(test_name)) == 1)
         else begin
            if((a_line != 0) && (a_filename != "")) begin
               
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_ERROR,"CHECK_SVA_ENABLED_ERR")) 
       uvm_report_error ("CHECK_SVA_ENABLED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg), UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_vpi_wrapper.svh", 792, "", 1); 
   end

            end else begin
               
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_ERROR,"CHECK_SVA_ENABLED_ERR")) 
       uvm_report_error ("CHECK_SVA_ENABLED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg), UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_vpi_wrapper.svh", 795, "", 1); 
   end

            end
         end
         add_check(assertion, "CHECK_SVA_ENABLED", $time(), get_current_check_status());
      end
   endfunction

      
   virtual function void check_sva_disabled(string a_sva_name, string a_error_msg = "The SVA should have been disabled.",
         int unsigned a_line = 0, string a_filename = "");

            svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         CHECK_SVA_DISABLED : assert(check_expression(assertion.sva_disabled(test_name)) == 1)
         else begin
            if((a_line != 0) && (a_filename != "")) begin
               
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_ERROR,"CHECK_SVA_ENABLED_ERR")) 
       uvm_report_error ("CHECK_SVA_ENABLED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg), UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_vpi_wrapper.svh", 820, "", 1); 
   end

            end else begin
               
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_ERROR,"CHECK_SVA_ENABLED_ERR")) 
       uvm_report_error ("CHECK_SVA_ENABLED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg), UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_vpi_wrapper.svh", 823, "", 1); 
   end

            end
         end
         add_check(assertion, "CHECK_SVA_DISABLED", $time(), get_current_check_status());
      end
   endfunction

      
   virtual function void check_sva_exists(string a_sva_name, string a_error_msg = "The SVA does not exist.",
         int unsigned a_line = 0, string a_filename = "");

            svaunit_concurrent_assertion_info assertion;
      if(is_a_path(a_sva_name)) begin
         assertion = vpi_vif.get_assertion_from_path(a_sva_name);
      end else begin
         assertion = vpi_vif.get_assertion_by_name(a_sva_name);
      end

      CHECK_SVA_EXISTS : assert((check_expression(assertion != null)) == 1)  begin
         assertion.set_tested(get_test_name());
      end else begin
         if((a_line != 0) && (a_filename != "")) begin
            
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_ERROR,"CHECK_SVA_ENABLED_ERR")) 
       uvm_report_error ("CHECK_SVA_ENABLED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg), UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_vpi_wrapper.svh", 853, "", 1); 
   end

         end else begin
            
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_ERROR,"CHECK_SVA_ENABLED_ERR")) 
       uvm_report_error ("CHECK_SVA_ENABLED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg), UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_vpi_wrapper.svh", 856, "", 1); 
   end

         end

         begin
            string sva_name = a_sva_name;
            string sva_path = "";
            string sva_type = "";

            assertion = svaunit_concurrent_assertion_info::type_id::create( "new_assertion");

            assertion.create_new_sva(sva_name, sva_path, sva_type);
         end
      end

      add_check(assertion, "CHECK_SVA_EXISTS", $time(), get_current_check_status());
   endfunction



      
   virtual task check_sva_passed(string a_sva_name, string a_error_msg = "The SVA should have passed.",
         int unsigned a_line = 0, string a_filename = "");

            svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         check_assertion_is_enabled(a_sva_name);

         CHECK_SVA_PASSED : assert(check_expression(assertion.sva_passed()) == 1)
         else begin
            if((a_line != 0) && (a_filename != "")) begin
               
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_ERROR,"CHECK_SVA_ENABLED_ERR")) 
       uvm_report_error ("CHECK_SVA_ENABLED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg), UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_vpi_wrapper.svh", 895, "", 1); 
   end

            end else begin
               
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_ERROR,"CHECK_SVA_ENABLED_ERR")) 
       uvm_report_error ("CHECK_SVA_ENABLED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg), UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_vpi_wrapper.svh", 898, "", 1); 
   end

            end
         end

         add_check(assertion, "CHECK_SVA_PASSED", $time(), get_current_check_status());
      end
   endtask



      
   virtual task check_sva_failed(string a_sva_name, string a_error_msg = "The SVA should have failed.",
         int unsigned a_line = 0, string a_filename = "");

            svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin

         check_assertion_is_enabled(a_sva_name);

         CHECK_SVA_FAILED :  assert(check_expression(!assertion.sva_passed()) == 1)
         else begin
            if((a_line != 0) && (a_filename != "")) begin
               
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_ERROR,"CHECK_SVA_ENABLED_ERR")) 
       uvm_report_error ("CHECK_SVA_ENABLED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg), UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_vpi_wrapper.svh", 929, "", 1); 
   end

            end else begin
               
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_ERROR,"CHECK_SVA_ENABLED_ERR")) 
       uvm_report_error ("CHECK_SVA_ENABLED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg), UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_vpi_wrapper.svh", 932, "", 1); 
   end

            end

         end

         add_check(assertion, "CHECK_SVA_FAILED", $time(), get_current_check_status());
      end
   endtask



      
   virtual task check_sva_finished(string a_sva_name, string a_error_msg = "The SVA should have finished.",
         int unsigned a_line = 0, string a_filename = "");

            svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         check_assertion_is_enabled(a_sva_name);

         CHECK_SVA_FINISHED : assert(check_expression(assertion.sva_finished()) == 1)
         else begin

            if((a_line != 0) && (a_filename != "")) begin
               
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_ERROR,"CHECK_SVA_ENABLED_ERR")) 
       uvm_report_error ("CHECK_SVA_ENABLED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg), UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_vpi_wrapper.svh", 964, "", 1); 
   end

            end else begin
               
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_ERROR,"CHECK_SVA_ENABLED_ERR")) 
       uvm_report_error ("CHECK_SVA_ENABLED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg), UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_vpi_wrapper.svh", 967, "", 1); 
   end

            end
         end

         add_check(assertion, "CHECK_SVA_FINISHED", $time(), get_current_check_status());
      end
   endtask


      
   virtual task check_sva_not_finished(string a_sva_name, string a_error_msg = "The SVA should not have finished.",
         int unsigned a_line = 0, string a_filename = "");

            svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         check_assertion_is_enabled(a_sva_name);

         CHECK_SVA_NOT_FINISHED : assert(check_expression(assertion.sva_not_finished()) == 1)
         else begin
            if((a_line != 0) && (a_filename != "")) begin
               
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_ERROR,"CHECK_SVA_ENABLED_ERR")) 
       uvm_report_error ("CHECK_SVA_ENABLED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg), UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_vpi_wrapper.svh", 996, "", 1); 
   end

            end else begin
               
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_ERROR,"CHECK_SVA_ENABLED_ERR")) 
       uvm_report_error ("CHECK_SVA_ENABLED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg), UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_vpi_wrapper.svh", 999, "", 1); 
   end

            end
         end

         add_check(assertion, "CHECK_SVA_NOT_FINISHED", $time(), get_current_check_status());
      end
   endtask



      
   virtual function void check_that(bit a_expression, string a_error_msg = "The expression should have passed.", int unsigned a_line = 0,
         string a_filename = "");

      svaunit_concurrent_assertion_info new_assertion = svaunit_concurrent_assertion_info::type_id::create(
         "new_assertion");
      string sva_name = "";
      string sva_path = "";
      string sva_type = "";

      new_assertion.create_new_sva(sva_name, sva_path, sva_type);

      CHECK_THAT : assert(check_expression(a_expression) == 1)
      else begin
         if((a_line != 0) && (a_filename != "")) begin
            
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_ERROR,"CHECK_SVA_ENABLED_ERR")) 
       uvm_report_error ("CHECK_SVA_ENABLED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg), UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_vpi_wrapper.svh", 1031, "", 1); 
   end

         end else begin
            
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_ERROR,"CHECK_SVA_ENABLED_ERR")) 
       uvm_report_error ("CHECK_SVA_ENABLED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg), UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_vpi_wrapper.svh", 1034, "", 1); 
   end

         end
      end

      add_check(new_assertion, "CHECK_THAT", $time(), get_current_check_status());
   endfunction


      virtual task pass_assertion();
      if(lof_checks.size() == 0) begin
         if(vpi_vif.sva_info.size() > 0) begin
            foreach(vpi_vif.sva_info[sva_index]) begin
               if(is_enable(vpi_vif.sva_info[sva_index].get_sva_name())) begin
                  check_sva_failed(vpi_vif.sva_info[sva_index].get_sva_name(), $sformatf(
                        "Assertion %s should have succeeded, found instead: %s",
                        vpi_vif.sva_info[sva_index].get_sva_name(), vpi_vif.sva_info[sva_index].get_sva_state()));
               end
            end
         end
      end
   endtask


   
   virtual function void check_all_sva_passed(string a_error_msg);

            bit all_succeeded = 1;

      foreach(vpi_vif.sva_info[sva_index]) begin
         if(vpi_vif.sva_info[sva_index].sva_enabled(get_test_name())) begin
            string sva_name = vpi_vif.sva_info[sva_index].get_sva_name();
            if((get_nof_times_assertion_failed(sva_name) != 0) ||
                  (get_nof_times_assertion_succeeded(sva_name) == 0)) begin
               all_succeeded = 0;
            end
         end
      end

      CHECK_ALL_SVA_PASSED : assert((check_expression(all_succeeded == 1)) == 1)
      else begin
         
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_ERROR,"CHECK_SVA_ENABLED_ERR")) 
       uvm_report_error ("CHECK_SVA_ENABLED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg), UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_vpi_wrapper.svh", 1078, "", 1); 
   end

      end

      foreach(vpi_vif.sva_info[sva_index]) begin
         if(vpi_vif.sva_info[sva_index].sva_enabled(get_test_name())) begin
            add_check(vpi_vif.sva_info[sva_index], "CHECK_ALL_SVA_PASSED", $time(),
               get_current_check_status());
         end
      end
   endfunction

   
   virtual function void print_status();
      string report = "";

      report = $sformatf("\n\n-------------------- %s : Status statistics --------------------", get_test_name());
      report = $sformatf("%s\n\t%s\n", report, get_status_as_string());

      
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_INFO,get_name())) 
       uvm_report_info (get_name(), text, UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_vpi_wrapper.svh", 1099, "", 1); 
   end

   endfunction

   
   virtual function string get_status_as_string();
      string star = " ";

            int unsigned nof_times_check_has_passed = 0;

            int unsigned nof_times_check_was_tested = 0;

            string checks_names[$];
      get_checks_names(lof_checks, checks_names);

            foreach(checks_names[index]) begin
         foreach(lof_checks[check_index]) begin
            foreach(lof_checks[check_index].checks_details[details_index])begin
               if(lof_checks[check_index].checks_details[details_index].get_check_name() == checks_names[index]) begin
                  nof_times_check_was_tested = nof_times_check_was_tested +
                  get_nof_times_check_was_tested(checks_names[index], lof_checks);
                  nof_times_check_has_passed = nof_times_check_has_passed +
                  get_nof_times_check_has_passed(checks_names[index], lof_checks);
               end
            end
         end
      end

      if(nof_times_check_was_tested > nof_times_check_has_passed) begin
         star = "* FAILED";
      end else begin
         star = "PASSED";
      end

      return $sformatf("\n\t%s   (%0d/%0d assertions PASSED)", star, nof_times_check_was_tested -
         nof_times_check_has_passed, nof_times_check_was_tested);
   endfunction

   
   virtual function void print_checks_from_specific_list(string a_test_name,
         ref svaunit_immediate_assertion_info a_lof_used_checks[$]);

      string report = "";
      string star = "";
      string extra = "";
      string lof_used_checks_names[$];
      string lof_not_used_checks_names[$];
      int unsigned nof_times_check_was_tested;
      int unsigned nof_times_check_has_passed;

      get_checks_names(a_lof_used_checks, lof_used_checks_names);
      get_checks_not_used_names(a_lof_used_checks, lof_not_used_checks_names);

      report = $sformatf("\n\n-------------------- %s: Checks status summary --------------------\n\n", a_test_name);

      foreach(lof_used_checks_names[index]) begin
         nof_times_check_was_tested = 0;
         nof_times_check_has_passed = 0;
         star = " ";
         extra = "";

         nof_times_check_was_tested = get_nof_times_check_was_tested(lof_used_checks_names[index], a_lof_used_checks);
         nof_times_check_has_passed = get_nof_times_check_has_passed(lof_used_checks_names[index], a_lof_used_checks);

         if(nof_times_check_has_passed < nof_times_check_was_tested) begin
            star = "*";
         end

         extra = $sformatf("%0d/%0d PASSED", nof_times_check_has_passed, nof_times_check_was_tested);

         report = $sformatf("%s\t   %s   %s %s \n", report, star, lof_used_checks_names[index], extra);
      end


      
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_INFO,get_name())) 
       uvm_report_info (get_name(), text, UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_vpi_wrapper.svh", 1181, "", 1); 
   end

   endfunction

      virtual function void print_checks();
      print_checks_from_specific_list(get_test_name(), lof_checks);
   endfunction

   
   virtual function void print_sva_and_checks_for_specific_list(ref string a_test_name,
         svaunit_immediate_assertion_info a_lof_used_checks[$]);

      string report = "";

      report = $sformatf("\n\n-------------------- %s: Checks for each SVA statistics --------------------\n", a_test_name);

      foreach(a_lof_used_checks[check_index]) begin
         report = $sformatf("%s\n\t%s", report, a_lof_used_checks[check_index].get_checks_for_sva());
      end

      report = $sformatf("%s", report);

      
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_INFO,get_name())) 
       uvm_report_info (get_name(), text, UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_vpi_wrapper.svh", 1206, "", 1); 
   end

   endfunction

      virtual function void print_sva_and_checks();
      string a_test_name = get_test_name();

      print_sva_and_checks_for_specific_list(a_test_name, lof_checks);
   endfunction

   
   virtual function void print_failed_sva_for_specific_list(ref string a_test_name,
         ref svaunit_immediate_assertion_info a_lof_used_checks[$]);

      string report = "";
      string details = "";

      foreach(a_lof_used_checks[check_index]) begin
         details = a_lof_used_checks[check_index].get_sva_failed_details();
         if(details != "") begin
            report = $sformatf("\n\n-------------------- %s: Failed SVAs --------------------\n", a_test_name);
            report = $sformatf("%s\n\t%s", report, a_lof_used_checks[check_index].get_sva_failed_details());
         end else begin
            report = $sformatf("\n\n-------------------- %s: All SVAs passed --------------------\n", a_test_name);
         end
      end

      report = $sformatf("%s", report);

      
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_INFO,get_name())) 
       uvm_report_info (get_name(), text, UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_vpi_wrapper.svh", 1238, "", 1); 
   end

   endfunction

      virtual function void print_failed_sva();
      string crt_test_name = get_test_name();

      print_failed_sva_for_specific_list(crt_test_name, lof_checks);
   endfunction

      virtual function void print_report();
      print_status();
      print_sva();
      print_checks();
      print_sva_and_checks();
      print_failed_sva();
   endfunction

      virtual function void print_sva();
      
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_INFO,get_name())) 
       uvm_report_info (get_name(), text, UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_vpi_wrapper.svh", 1259, "", 1); 
   end

   endfunction

   
   virtual function void print_sva_info(ref string a_sva_name);
      svaunit_concurrent_assertion_info assertion = get_assertion_by_name(a_sva_name);

      vpi_vif.get_info_from_c(get_test_name());

      if(assertion != null) begin
         assertion.print_sva_info(get_test_name());
      end
   endfunction
endclass


/* SLline 57 "../../../UVM/svaunit/sv/svaunit_pkg.sv" 2 */

// Definition of SVAUnit base class
/* SLline 1 "../../../UVM/svaunit/sv/svaunit_base.svh" 1 */



class svaunit_base extends uvm_test;
		bit enable;

		bit stop_test;

	
   
   typedef uvm_component_registry #(svaunit_base,"svaunit_base") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction
 
   
   const static string type_name = "svaunit_base"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 


		local svaunit_status_type test_status;

		local bit has_started;

		local int unsigned nof_failures;

		local int unsigned nof_tests;

		local string test_name;

		local string test_type;

		svaunit_immediate_assertion_info lof_checks[$];

		svaunit_vpi_wrapper vpiw;

		string sequence_name[$];

	
	function new(string name = "svaunit_base", uvm_component parent);
		super.new(name, parent);

				nof_failures = 0;
		nof_tests = 0;
		has_started = 0;
		stop_test = 0;
		enable = 1;
	endfunction

	
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);

				if (!uvm_config_db#(svaunit_vpi_wrapper)::get(uvm_root::get(), "*", "VPIW", vpiw)) begin
			
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_FATAL,"SVAUNIT_VPI_WRAPPER_NO_VIF_ERR")) 
       uvm_report_fatal ("SVAUNIT_VPI_WRAPPER_NO_VIF_ERR", 
            "SVAUnit VPI interface for vpi_wrapper class is not set! Please enable SVAUnit package!", UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_base.svh", 84, "", 1); 
   end

		end

		set_test_name();
	endfunction

	
	virtual function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
	endfunction

	
	virtual function void update_test_name(string a_test_name);
		test_name = a_test_name;
	endfunction

		virtual function void set_test_name();
	endfunction

	
	virtual function void set_name_for_test();
				uvm_component parent = get_parent();

		if(parent.get_name() == "") begin
			test_name = $sformatf("%s", get_type_name());
		end else begin
			if(parent.get_name() == "uvm_test_top") begin
				test_name = $sformatf("%s.%s", parent.get_type_name(), get_name());
			end else begin
				if(get_name() == "uvm_test_top") begin
					test_name = $sformatf("%s", get_name());
				end else begin
					test_name = $sformatf("%s.%s", parent.get_name(), get_name());
				end
			end
		end
	endfunction

	
	virtual function string get_test_name();
		return test_name;
	endfunction


		virtual function void start_of_simulation();
				svaunit_reporter sva_unit_server = svaunit_reporter::type_id::create("sva_unit_server", this);
		uvm_report_server::set_server(sva_unit_server);
	endfunction

	
	virtual function int unsigned get_nof_tests();
		return nof_tests;
	endfunction

	
	virtual function void set_nof_tests(int unsigned a_nof_tests);
		nof_tests = a_nof_tests;
	endfunction

	
	virtual function string get_test_type();
		return test_type;
	endfunction

	
	virtual function void set_test_type(string a_test_type);
		test_type = a_test_type;
	endfunction


	
	virtual function int unsigned get_nof_failures();
		return nof_failures;
	endfunction

	
	virtual function void set_nof_failures(int unsigned a_nof_failures);
		nof_failures = a_nof_failures;
	endfunction

		virtual function void start_test();
		has_started = 1;
	endfunction

	
	virtual function bit started();
		return has_started;
	endfunction

	
	virtual function svaunit_status_type get_status();
		return test_status;
	endfunction

	
	virtual function void set_status(svaunit_status_type a_status);
		test_status = a_status;
	endfunction

	
	virtual function bit get_stop();
		return stop_test;
	endfunction

	
	virtual function svaunit_status_type compute_status(int unsigned a_nof_tests, int unsigned a_nof_failures);
				int unsigned nof_tests_not_run = 0;

		nof_tests_not_run = get_nof_tests_did_not_run();

								if(a_nof_failures == 0) begin
			if((a_nof_tests == 0) || (nof_tests_not_run == a_nof_tests)) begin
				return SVAUNIT_DID_NOT_RUN;
			end else begin
				return SVAUNIT_PASS;
			end
		end else begin
			return SVAUNIT_FAIL;
		end
	endfunction

		virtual function void update_status();
	endfunction

	
	virtual function int unsigned get_nof_tests_did_not_run();
		return 0;
	endfunction

		
	virtual function void get_checks_names(ref string a_lof_used_checks[$]);
	endfunction


	
	virtual function int unsigned get_nof_times_check_was_tested(ref string a_check_name);
		return 0;
	endfunction

	
	virtual function int unsigned get_nof_times_check_has_passed(ref string a_check_name);
		return 0;
	endfunction
	
	
		virtual function void print_tests();
	endfunction

		virtual function void print_status();
	endfunction

	
	virtual function void get_sva_tested_names(ref string a_tested_sva_names[$]);
	endfunction

	
	virtual function void get_sva_not_tested_names(ref string a_sva_not_tested[$]);
	endfunction

		virtual function void print_sva();
				string nice_string = "";

				string tested_sva_names[$];

				string sva_not_tested[$];

				int unsigned nof_tested_sva;

				int unsigned nof_sva_not_tested;

		get_sva_tested_names(tested_sva_names);
		get_sva_not_tested_names(sva_not_tested);

		nof_tested_sva = tested_sva_names.size();
		nof_sva_not_tested = sva_not_tested.size();

				nice_string = $sformatf("\n\n-------------------- %s: Exercised SVAs --------------------\n", get_test_name());
		nice_string = $sformatf("%s\n\t%0d/%0d SVA were exercised", nice_string, nof_tested_sva,
			nof_sva_not_tested + nof_tested_sva);

		foreach(tested_sva_names[index]) begin
			nice_string = $sformatf("%s\n\t\t%s", nice_string, tested_sva_names[index]);
		end

						if(nof_sva_not_tested > 0) begin
			nice_string = $sformatf("%s\n\n\t%0d SVA were not exercised", nice_string, nof_sva_not_tested);

			foreach(sva_not_tested[index]) begin
				nice_string = $sformatf("%s\n\t\t%s", nice_string, sva_not_tested[index]);
			end
		end

		nice_string = $sformatf("%s\n\n", nice_string);

		
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_INFO,get_name())) 
       uvm_report_info (get_name(), text, UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_base.svh", 349, "", 1); 
   end

	endfunction

	
	virtual function void get_checks(ref svaunit_immediate_assertion_info a_checks[$]);
	endfunction

		virtual function void print_checks();
		vpiw.print_checks_from_specific_list(get_test_name(), lof_checks);
	endfunction

		virtual function void print_sva_and_checks();
		string a_test_name = get_test_name();

		vpiw.print_sva_and_checks_for_specific_list(a_test_name, lof_checks);
	endfunction

		virtual function void print_failed_sva();
		string crt_test_name = get_test_name();

		vpiw.print_failed_sva_for_specific_list(crt_test_name, lof_checks);
	endfunction

	
	virtual function string form_tree(int a_level);
	endfunction

		virtual function void print_tree();
		string nice_string = "";

		nice_string = $sformatf("\n\n-------------------- %s test suite: Project hierarchy --------------------\n", get_test_name());
		nice_string = {nice_string, $sformatf("\n%s", form_tree(0)), "\n\n"};

		
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_INFO,get_name())) 
       uvm_report_info (get_name(), text, UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_base.svh", 391, "", 1); 
   end

	endfunction

		virtual function void print_report();
		print_tree();
		print_status();
		print_tests();
		print_sva();
		print_checks();
		print_sva_and_checks();
		print_failed_sva();
	endfunction
endclass


/* SLline 60 "../../../UVM/svaunit/sv/svaunit_pkg.sv" 2 */

// Definition of SVAUnit virtual sequencer class and definition of SVAUnit base sequence class
/* SLline 1 "../../../UVM/svaunit/sv/svaunit_sequence.svh" 1 */



class svaunit_sequencer extends uvm_virtual_sequencer;
   
   
   typedef uvm_component_registry #(svaunit_base,"svaunit_base") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction
 
   
   const static string type_name = "svaunit_base"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 


      svaunit_vpi_wrapper vpiw;

   
   function new(string name = "svaunit_sequencer", uvm_component parent);
      super.new(name, parent);
   endfunction

   
   virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);

            if (!uvm_config_db#(svaunit_vpi_wrapper)::get(uvm_root::get(), "*", "VPIW", vpiw)) begin
         
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_FATAL,"SVAUNIT_VPI_WRAPPER_NO_VIF_ERR")) 
       uvm_report_fatal ("SVAUNIT_VPI_WRAPPER_NO_VIF_ERR", 
            "SVAUnit VPI interface for vpi_wrapper class is not set! Please enable SVAUnit package!", UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_sequence.svh", 47, "", 1); 
   end

      end
      
   endfunction
endclass

class svaunit_base_sequence extends uvm_sequence;
   
  
   
   typedef uvm_object_registry#(svaunit_reporter,"svaunit_reporter") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction 
  
   
   function uvm_object create (string name=""); 
     svaunit_reporter tmp; 
     if (name=="") tmp = new(); 
     else tmp = new(name); 
     return tmp; 
   endfunction
 
   
   const static string type_name = "svaunit_reporter"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 
   
   function void __m_uvm_field_automation (uvm_object tmp_data__, 
                                     int what__, 
                                     string str__); 
   begin 
     svaunit_reporter local_data__; /* Used for copy and compare */ 
     typedef svaunit_reporter ___local_type____; 
     string string_aa_key; /* Used for associative array lookups */ 
     uvm_object __current_scopes[$]; 
     if(what__ inside {UVM_SETINT,UVM_SETSTR,UVM_SETOBJ}) begin 
        if(__m_uvm_status_container.m_do_cycle_check(this)) begin 
            return; 
        end 
        else 
            __current_scopes=__m_uvm_status_container.m_uvm_cycle_scopes; 
     end 
     super.__m_uvm_field_automation(tmp_data__, what__, str__); 
     /* Type is verified by uvm_object::compare() */ 
     if(tmp_data__ != null) 
       /* Allow objects in same hierarchy to be copied/compared */ 
       if(!$cast(local_data__, tmp_data__)) return;
 
 
  
     end 
   endfunction 


   
  svaunit_sequencer p_sequencer;
  virtual function void m_set_p_sequencer();
    super.m_set_p_sequencer(); 
    if( !$cast(p_sequencer, m_sequencer)) 
        
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_FATAL,"SVAUNIT_VPI_WRAPPER_NO_VIF_ERR")) 
       uvm_report_fatal ("SVAUNIT_VPI_WRAPPER_NO_VIF_ERR", 
            "SVAUnit VPI interface for vpi_wrapper class is not set! Please enable SVAUnit package!", UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_sequence.svh", 57, "", 1); 
   end
 
  endfunction  


      svaunit_vpi_wrapper vpiw;

      bit stop_test;

      local string test_name;

      local string child_name[$];

      local svaunit_immediate_assertion_info lof_checks[$];

      local bit update_lof_checks;

   
   function new(string name = "svaunit_base_sequence");
      super.new(name);

            if (!uvm_config_db#(svaunit_vpi_wrapper)::get(uvm_root::get(), "*", "VPIW", vpiw)) begin
         
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_FATAL,"SVAUNIT_VPI_WRAPPER_NO_VIF_ERR")) 
       uvm_report_fatal ("SVAUNIT_VPI_WRAPPER_NO_VIF_ERR", 
            "SVAUnit VPI interface for vpi_wrapper class is not set! Please enable SVAUnit package!", UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_sequence.svh", 85, "", 1); 
   end

      end

      update_lof_checks = 0;
      stop_test = 0;
   endfunction

   
   virtual function bit get_stop();
      return stop_test;
   endfunction
   

   
   local function void get_checks(ref svaunit_immediate_assertion_info a_checks[$]);
      if(update_lof_checks == 0) begin
         vpiw.get_checks_for_test(get_test_name(), a_checks);

                  foreach(child_name[child_index]) begin
            vpiw.get_checks_for_test(child_name[child_index], a_checks);
         end

         update_lof_checks = 1;
      end
   endfunction

   
   virtual function string form_tree(int a_level);
      string extra = "";
      string report = "";

      for(int level_idx = 0; level_idx < (a_level - 1); level_idx++) begin
         extra = {"\t", extra};
      end

      if(a_level == 0) begin
         extra = {"\t", extra};
      end

      report = {extra, get_test_name()};

      foreach(child_name[index]) begin
         extra = "";
         for(int level_idx = 0; level_idx < (a_level + index + 2) ; level_idx++) begin
            extra = {"\t", extra};
         end

         report = {report, "\n", extra, child_name[index]};
      end

      return report;
   endfunction

      virtual task pre_start();
      uvm_sequence_base parent;
      svaunit_base_sequence seq_parent;
      string current_test_name;

      super.pre_start();

      parent = get_parent_sequence();

      if(parent != null) begin
         if(parent.get_name() == "") begin
            current_test_name = $sformatf("%s", get_name());
         end else begin
            if(parent.get_name() == "uvm_test_top") begin
               current_test_name = $sformatf("%s.%s", parent.get_type_name(), get_name());
            end else begin
               if(get_name() == "uvm_test_top") begin
                  current_test_name = $sformatf("%s", get_name());
               end else begin
                  if($cast(seq_parent, parent)) begin
                     current_test_name = $sformatf("%s.%s", seq_parent.get_test_name(), get_name());

                     child_name.push_back($sformatf("%s", current_test_name));
                     set_child_name(child_name[child_name.size() - 1]);
                  end
               end
            end
         end
      end else begin
         current_test_name = get_name();
      end

      set_test_name(current_test_name);
      vpiw.set_test_name_vpi(current_test_name);

      begin
         uvm_component seqr_parent = p_sequencer.get_parent();
         svaunit_base test;

         if($cast(test, seqr_parent)) begin
            test.sequence_name.push_back(current_test_name);
         end
      end
   endtask

      virtual function void print_checks();
      get_checks(lof_checks);
      vpiw.print_checks_from_specific_list(get_test_name(), lof_checks);
   endfunction

      virtual function void print_sva_and_checks();
      string a_test_name = get_test_name();

      get_checks(lof_checks);
      vpiw.print_sva_and_checks_for_specific_list(a_test_name, lof_checks);
   endfunction

      virtual function void print_failed_sva();
      string crt_test_name = get_test_name();

      get_checks(lof_checks);
      vpiw.print_failed_sva_for_specific_list(crt_test_name, lof_checks);
   endfunction

      virtual function void print_tree();
      string report = "";
      get_checks(lof_checks);

      report = $sformatf("\n%s", form_tree(0));

      
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_INFO,get_name())) 
       uvm_report_info (get_name(), text, UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_sequence.svh", 222, "", 1); 
   end

   endfunction

      virtual function void print_tests();
      get_checks(lof_checks);
   endfunction

      virtual function void print_status();
      get_checks(lof_checks);
   endfunction

   
   local function void get_sva_tested_names(ref string a_tested_sva_names[$]);
      svaunit_concurrent_assertion_info tested_sva[$];
      
      foreach(child_name[child_index]) begin
         vpiw.get_sva_tested(child_name[child_index], tested_sva);
         vpiw.get_sva_tested_names(tested_sva, a_tested_sva_names);
      end
   endfunction

   
   local function void get_sva_not_tested_names(ref string a_not_tested_sva[$]);
            string tested_sva_names[$];

            string lof_not_tested_sva[$];

      int not_tested_index[$];
      int n_tested_index[$];
      
      svaunit_concurrent_assertion_info not_tested_sva[$];
      
      foreach(child_name[child_index]) begin
         vpiw.get_sva_not_tested(child_name[child_index], not_tested_sva);
         vpiw.get_sva_not_tested_names(not_tested_sva, lof_not_tested_sva);
      end

            get_sva_tested_names(tested_sva_names);

      foreach(lof_not_tested_sva[sva_index]) begin
         n_tested_index = tested_sva_names.find_index() with (item == lof_not_tested_sva[sva_index]);

         if(n_tested_index.size() == 0) begin
            not_tested_index = a_not_tested_sva.find_index() with
            (item == lof_not_tested_sva[sva_index]);

            if(not_tested_index.size() == 0) begin
               a_not_tested_sva.push_back(lof_not_tested_sva[sva_index]);
            end
         end
      end
   endfunction

      virtual function void print_sva();
            string report = "";

            string tested_sva_names[$];

            string not_tested_sva[$];

            int unsigned nof_tested_sva;

            int unsigned nof_not_tested_sva;

      get_sva_tested_names(tested_sva_names);
      get_sva_not_tested_names(not_tested_sva);

      nof_tested_sva = tested_sva_names.size();
      nof_not_tested_sva = not_tested_sva.size();

            report = $sformatf("\n\n-------------------- %s : SVAs statistics --------------------\n", get_test_name());
      report = $sformatf("%s\n\t%0d/%0d SVA were exercised",
         report, nof_tested_sva, nof_not_tested_sva + nof_tested_sva);

      foreach(tested_sva_names[index]) begin
         report = $sformatf("%s\n\t\t%s", report, tested_sva_names[index]);
      end

                  if(nof_not_tested_sva > 0) begin
         report = $sformatf("%s\n\n\t%0d SVA were not exercised", report, nof_not_tested_sva);

         foreach(not_tested_sva[index]) begin
            report = $sformatf("%s\n\t\t%s", report, not_tested_sva[index]);
         end
      end

      report = $sformatf("%s\n", report);

      
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_INFO,get_name())) 
       uvm_report_info (get_name(), text, UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_sequence.svh", 328, "", 1); 
   end

   endfunction

      virtual function void print_report();
      get_checks(lof_checks);

      print_tree();
      print_status();
      print_tests();
      print_sva();
      print_checks();
      print_sva_and_checks();
      print_failed_sva();
   endfunction

   
   local function void set_child_name(string a_child_name);
      uvm_sequence_base parent;
      svaunit_base_sequence seq_parent;

      parent = get_parent_sequence();

      if(parent != null) begin
         if($cast(seq_parent, parent)) begin
            seq_parent.child_name.push_back($sformatf("%s",a_child_name));
            seq_parent.set_child_name(a_child_name);
         end
      end
   endfunction


   
   local function void set_test_name(string a_test_name);
      test_name = a_test_name;
   endfunction

   
   virtual function string get_test_name();
      return test_name;
   endfunction

      virtual task body();
      
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_INFO,get_name())) 
       uvm_report_info (get_name(), text, UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_sequence.svh", 378, "", 1); 
   end

   endtask
endclass


/* SLline 63 "../../../UVM/svaunit/sv/svaunit_pkg.sv" 2 */

// Definition of SVAUnit test class
/* SLline 1 "../../../UVM/svaunit/sv/svaunit_test.svh" 1 */



class svaunit_test extends svaunit_base;
   
   
   typedef uvm_component_registry #(svaunit_base,"svaunit_base") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction
 
   
   const static string type_name = "svaunit_base"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 


      local time timeout;

      svaunit_sequencer sequencer;

   
   function new(string name = "svaunit_test", uvm_component parent);
      super.new(name, parent);
      timeout = 10us;
   endfunction

   
   virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      sequencer = svaunit_sequencer::type_id::create("sequencer", this);

      if(get_test_name() == "")
         set_name_for_test();
   endfunction

   
   virtual function bit was_started_from_test_suite();
            uvm_component parent = get_parent();

                  if((!started()) && (parent.get_name() == "")) begin
         return 0;
      end else begin
         return 1;
      end
   endfunction

      virtual function void update_status();
            int unsigned nof_times_check_passed = 0;

            int unsigned nof_times_check_tested = 0;

            string checks_names[$];
      get_checks_names(checks_names);

            foreach(checks_names[index]) begin
         string crt_check_name = checks_names[index];

         foreach(lof_checks[check_index]) begin
            foreach(lof_checks[check_index].checks_details[details_index])begin
               if(lof_checks[check_index].checks_details[details_index].get_check_name() == checks_names[index]) begin
                  nof_times_check_tested = nof_times_check_tested + get_nof_times_check_was_tested(crt_check_name);
                  nof_times_check_passed = nof_times_check_passed + get_nof_times_check_has_passed(crt_check_name);
               end
            end
         end
      end

            set_nof_tests(nof_times_check_tested);
      set_nof_failures(nof_times_check_tested - nof_times_check_passed);

            vpiw.update_coverage();

      set_status(compute_status(get_nof_tests(), get_nof_failures()));
   endfunction

      virtual function void enable_test();
      enable = 1;
   endfunction

      virtual function void disable_test();
      enable = 0;
   endfunction

   
   
   virtual function void get_checks(ref svaunit_immediate_assertion_info a_checks[$]);
      if(sequence_name.size() > 0) begin
                  foreach(sequence_name[index]) begin
            vpiw.get_checks_for_test(sequence_name[index], a_checks);
         end
      end else begin
                  vpiw.get_checks_for_test(get_test_name(), a_checks);
      end
   endfunction

   
   virtual function void get_checks_names(ref string a_lof_used_checks[$]);
            foreach(lof_checks[check_index]) begin
         lof_checks[check_index].get_checks_names(a_lof_used_checks);
      end
   endfunction

   
   virtual function int unsigned get_nof_checks();
      return lof_checks.size();
   endfunction

   
   virtual function int unsigned get_nof_times_check_was_tested(ref string a_check_name);
            int unsigned nof_times_check_tested = 0;

                  foreach(lof_checks[check_index]) begin
         foreach(lof_checks[check_index].checks_details[details_index])begin
            if(lof_checks[check_index].checks_details[details_index].get_check_name() == a_check_name) begin
               nof_times_check_tested = nof_times_check_tested +
               lof_checks[check_index].checks_details[details_index].get_nof_times_check_was_tested();
            end
         end
      end

      return nof_times_check_tested;
   endfunction

   
   virtual function int unsigned get_nof_times_check_has_passed(ref string a_check_name);
            int unsigned nof_times_check_passed = 0;

                  foreach(lof_checks[check_index]) begin
         foreach(lof_checks[check_index].checks_details[details_index])begin
            if(lof_checks[check_index].checks_details[details_index].get_check_name() == a_check_name) begin
               nof_times_check_passed = nof_times_check_passed +
               lof_checks[check_index].checks_details[details_index].get_nof_times_check_has_passed();
            end
         end
      end

      return nof_times_check_passed;
   endfunction
   
   
   
   virtual function void get_sva_tested(ref svaunit_concurrent_assertion_info a_sva_tested[$]);
      if(sequence_name.size() > 0) begin
                  foreach(sequence_name[index]) begin
            vpiw.get_sva_tested(sequence_name[index], a_sva_tested);
         end
      end else begin
                  vpiw.get_sva_tested(get_test_name(), a_sva_tested);
      end
   endfunction

   
   virtual function int unsigned get_nof_sva();
      return vpiw.get_nof_sva();
   endfunction

   
   virtual function int unsigned get_nof_tested_sva();
      return vpiw.get_nof_tested_sva(get_test_name());
   endfunction

   
   virtual function void get_sva_tested_names(ref string a_tested_sva_names[$]);
      svaunit_concurrent_assertion_info tested_sva[$];

            get_sva_tested(tested_sva);

      vpiw.get_sva_tested_names(tested_sva, a_tested_sva_names);
   endfunction

   
   virtual function void get_sva_not_tested_names(ref string a_sva_not_tested[$]);
      svaunit_concurrent_assertion_info not_tested_sva[$];

            get_sva_not_tested(not_tested_sva);

      vpiw.get_sva_not_tested_names(not_tested_sva, a_sva_not_tested);
   endfunction

   
   virtual function void get_sva_not_tested(ref svaunit_concurrent_assertion_info a_sva_not_tested[$]);
      if(sequence_name.size() > 0) begin
                  foreach(sequence_name[index]) begin
            vpiw.get_sva_not_tested(sequence_name[index], a_sva_not_tested);
         end
      end else begin
                  vpiw.get_sva_not_tested(get_test_name(), a_sva_not_tested);
      end
   endfunction
   
   

      virtual task setup_test();
   endtask

      virtual task test();
   endtask

   
   virtual function void set_test_name_vpi(string a_test_name);
      vpiw.set_test_name_vpi(a_test_name);
   endfunction

      virtual task start_ut();
      if(enable == 1) begin
         start_test();
         set_test_name_vpi(get_test_name());
         vpiw.stop_test = 0;

         fork
            begin
                              process simulate_test;
               fork
                  begin
                     simulate_test = process::self();
                     fork
                        begin
                           setup_test();
                           vpiw.enable_all_assertions();
                           test();

                           vpiw.pass_assertion();
                        end
                        begin
                           int unsigned time_left = timeout;
                           while(time_left != 0) begin
                              #1ns;
                              time_left = time_left - 1;
                           end
                           
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_ERROR,"CHECK_SVA_ENABLED_ERR")) 
       uvm_report_error ("CHECK_SVA_ENABLED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg), UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_test.svh", 313, "", 1); 
   end

                        end
                        begin
                           while(stop_test == 0) begin
                              #1ns;

                              stop_test = vpiw.stop_test;
                           end
                        end
                     join_any
                  end
               join
               disable fork;
               simulate_test.kill();
            end
         join

                  get_checks(lof_checks);

                  update_status();
      end
   endtask

   
   virtual task run_phase(uvm_phase phase);
            if(was_started_from_test_suite() == 0) begin
                  uvm_test_done.raise_objection(this, "", 1);

                  if(enable == 1) begin
            fork
               begin
                                    process start_ut_p;
                  fork
                     begin
                        start_ut_p = process::self();
                        start_ut();
                        disable fork;
                     end
                  join
                  start_ut_p.kill();
               end
            join
            print_report();
            create_html_report();
         end

                  uvm_test_done.drop_objection(this, "", 1);
      end
   endtask

   
   virtual function string get_user_name();
            string user_name;

            int file_id;

            int read_id;

            $system("echo $USER > svaunit_user_name.date");

            file_id = $fopen("svaunit_user_name.date", "r");

            read_id = $fgets(user_name, file_id);

            $fclose(file_id);

      return user_name.substr(0, user_name.len() - 2);
   endfunction

   
   virtual function string get_date_with_format(string a_date_format);
            string date;

            int file_id;

            int read_id;

            $system($sformatf("date +%s > svaunit.date", a_date_format));

            file_id = $fopen("svaunit.date", "r");

            read_id = $fgets(date, file_id);

            $fclose(file_id);

      return date.substr(0, date.len() - 2);
   endfunction

   
   virtual function string create_html_header();
      return $sformatf("Automatically generated on %s by %s with %s",
         get_date_with_format("%Y-%m-%d"), get_user_name(), "`SVAUNIT_NAME.`SVAUNIT_MAJOR_REV.`SVAUNIT_MINOR_REV");
   endfunction

   
   virtual function string create_html_style();
      return $sformatf("<!DOCTYPE html>                                                   \n\
            <html>                                                                        \n\
            <head>                                                                        \n\
            <title>SVAUnit %s report</title>                                              \n\
            <style>                                                                       \n\
            /*Blog Page*/                                                                 \n\
            h2 {                                                                          \n\
               color: #555;                                                               \n\
               font-size: 21px;                                                           \n\
               line-height: 32px;                                                         \n\
               margin-bottom: 10px;                                                       \n\
            }                                                                             \n\
            h2 a {                                                                        \n\
               color: #585f69;                                                            \n\
               line-height: 32px;                                                         \n\
            }                                                                             \n\
            a:focus  {                                                                    \n\
               color: #ee3424;                                                            \n\
            }                                                                             \n\
            .color-green {                                                                \n\
               color: #ee3424;                                                            \n\
            }                                                                             \n\
                                                                                          \n\
            a.read-more:hover {                                                           \n\
               color:#ee3424;                                                             \n\
            }                                                                             \n\
                                                                                          \n\
            .linked:hover {                                                               \n\
               color:#ee3424;                                                             \n\
            }                                                                             \n\
            h2 a:hover {                                                                  \n\
               color: #72c02c;                                                            \n\
               text-decoration: none;                                                     \n\
            }                                                                             \n\
                                                                                          \n\
            .headline-md {                                                                \n\
               margin-top: 9px;                                                           \n\
            }                                                                             \n\
            body {                                                                        \n\
               color: #000333;                                                            \n\
               font-size: 13px;                                                           \n\
               line-height: 1.6;                                                          \n\
            }                                                                             \n\
            p,                                                                            \n\
            li,                                                                           \n\
            li a,                                                                         \n\
            label {                                                                       \n\
               color: #555;                                                               \n\
            }                                                                             \n\
            span {                                                                        \n\
               color: #777;                                                               \n\
               font-size: 12px;                                                           \n\
               position: absolute;                                                        \n\
            }                                                                             \n\
            table, th, td {                                                               \n\
               border: 1px solid black;                                                   \n\
               border-collapse: collapse;                                                 \n\
               vertical-align: middle;                                                    \n\
               color: #00355f;                                                            \n\
            }                                                                             \n\
                                                                                          \n\
            p {                                                                           \n\
               font-family: \"Times New Roman\";                                          \n\
            }                                                                             \n\
            </style>                                                                      \n\
            </head>                                                                       \n", get_test_name());
   endfunction

      virtual function void create_html_report();
            int fileid;

            string report_name = $sformatf("svaunit_%s_report_%s.html", get_test_name(), get_date_with_format("%Y%m%d"));

      fileid = $fopen(report_name);

            if (fileid == 0) begin
         
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_ERROR,"CHECK_SVA_ENABLED_ERR")) 
       uvm_report_error ("CHECK_SVA_ENABLED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg), UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_test.svh", 521, "", 1); 
   end
;
      end else begin
                  string checks_names[$];

                  string tested_sva_names[$];

                  string not_tested_sva_names[$];

                  string svaunit_report;

                  int unsigned total_nof_failing_checks;

                  int unsigned total_nof_passing_checks;

         get_sva_tested_names(tested_sva_names);
         get_sva_not_tested_names(not_tested_sva_names);
         get_checks_names(checks_names);

         foreach(tested_sva_names[index]) begin
            foreach(checks_names[check_index]) begin
               foreach(lof_checks[an_index]) begin
                  if(lof_checks[an_index].sva_tested.get_sva_path() == tested_sva_names[index]) begin
                     foreach(lof_checks[an_index].checks_details[details_index]) begin
                        string check_name = lof_checks[an_index].checks_details[details_index].get_check_name();
                        if(check_name == checks_names[check_index]) begin
                           int nof_check_passed =
                           lof_checks[an_index].checks_details[details_index].get_nof_times_check_has_passed();
                           int nof_check_tested =
                           lof_checks[an_index].checks_details[details_index].get_nof_times_check_was_tested();

                           if(nof_check_passed == nof_check_tested) begin
                                                            total_nof_passing_checks = total_nof_passing_checks + 1;
                           end else begin
                                                            total_nof_failing_checks = total_nof_failing_checks + 1;
                           end
                        end
                     end
                  end
               end
            end

            svaunit_report = $sformatf("Total number of SVAs: %0d<br />\
                                       Exercised SVAs: %0d<br />\
                                       Executed checks: %0d<br />\
                                       Failing checks: %0d<br />\
                                       Passing checks: %0d<br />\n",
               (tested_sva_names.size() + not_tested_sva_names.size()), tested_sva_names.size(),
               total_nof_failing_checks + total_nof_passing_checks, total_nof_failing_checks,
               total_nof_passing_checks);
         end

         $fwrite(fileid, $sformatf("%s\n<body>                                                   \n\
            <h2>SVAUnit regression report</h2>                                                   \n\
            <p>%s</p>\n<p>%s</p>                                                                 \n\
            <table border=\"0\" cellspacing=\"0\">                                               \n\
            <colgroup width=\"%0d\"></colgroup>\n<colgroup span=\"%0d\"></colgroup> \n\
            <tbody>\n<tr>                                                                        \n\
            <td style=\"border: 1px solid #ffffff;\" align=\"RIGHT\" height=\"28\"></td>         \n\
            <td style=\"border-bottom: 1px solid #ffffff; border-left: 1px solid #ffffff;          \
               border-top: 1px solid #ffffff;\" align=\"RIGHT\"></td>                            \n\
            <td colspan=\"%0d\" align=\"CENTER\"><b>SVAUnit checks</b></td>\n</tr>\n<tr>         \n\
            <td style=\"border-right: 1px solid #ffffff; border-left: 1px solid #ffffff;\"         \
               align=\"RIGHT\" height=\"28\"></td>\n<td align=\"RIGHT\"></td>", create_html_style(),
               create_html_header(), svaunit_report, checks_names.size(), checks_names.size(), checks_names.size()));

         foreach(checks_names[index]) begin
            $fwrite(fileid, $sformatf("<td align=\"CENTER\"><b>%s</b></td>\n", checks_names[index]));
         end
         $fwrite(fileid, $sformatf("</tr>\n<tr>\n\
            <td rowspan=\"%0d\" align=\"CENTER\" height=\"%0d\"><b>S<br />V<br />A<br />s<br /></b></td>\n",
               (tested_sva_names.size() + not_tested_sva_names.size() + 1), tested_sva_names.size() + 1));

         foreach(tested_sva_names[index]) begin
            string cell_symbol;
            svaunit_concurrent_assertion_info crt_sva = vpiw.get_assertion(tested_sva_names[index]);

            $fwrite(fileid, $sformatf("<tr><td align=\"LEFT\"><b><a title=\"%s\">%s</a></b></td>\n",
                  tested_sva_names[index], crt_sva.get_sva_name()));

            foreach(checks_names[check_index]) begin
               bit check_has_been_used = 0;

               foreach(lof_checks[an_index]) begin
                  if(lof_checks[an_index].sva_tested.get_sva_path() == tested_sva_names[index]) begin
                     foreach(lof_checks[an_index].checks_details[details_index]) begin
                        string check_name = lof_checks[an_index].checks_details[details_index].get_check_name();
                        if(check_name == checks_names[check_index]) begin
                           int nof_check_passed =
                           lof_checks[an_index].checks_details[details_index].get_nof_times_check_has_passed();
                           int nof_check_tested =
                           lof_checks[an_index].checks_details[details_index].get_nof_times_check_was_tested();
                           check_has_been_used = 1;

                                                      if(nof_check_passed == nof_check_tested) begin
                              cell_symbol = "bgcolor=\"#c6efce\">&#x2713;";
                           end else begin
                                                            cell_symbol = "bgcolor=\"#ee3424\">&#x2717;";
                           end
                        end
                     end
                  end
               end

                              if(check_has_been_used == 0) begin
                  cell_symbol = "bgcolor=\"#fff3cf\">?";
               end
               $fwrite(fileid, $sformatf("<td align=\"CENTER\" %s</td>\n", cell_symbol));
            end
            $fwrite(fileid,"</tr>\n");
         end

         foreach(not_tested_sva_names[index]) begin
            svaunit_concurrent_assertion_info crt_sva = vpiw.get_assertion(not_tested_sva_names[index]);

            $fwrite(fileid, $sformatf("<tr>\n\
               <td align=\"LEFT\"><b><a title=\"%s\">%s</a></b></td>\n",
                  not_tested_sva_names[index], crt_sva.get_sva_name()));

            foreach(checks_names[check_index]) begin
                              $fwrite(fileid, "<td align=\"CENTER\" bgcolor=\"#fff3cf\">?</td>\n");
            end
            $fwrite(fileid,"</tr>\n");
         end
         $fwrite(fileid, "</tbody>\n</table>\n</body>\n</html>\n");
         $fclose(fileid);
      end
   endfunction
   
   
      virtual function void print_status();
      string nice_string = "";

      nice_string = $sformatf("\n\n-------------------- %s : Status statistics --------------------", get_test_name());
      nice_string = $sformatf("%s\n\t%s\n", nice_string, get_status_as_string());

      
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_INFO,get_name())) 
       uvm_report_info (get_name(), text, UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_test.svh", 671, "", 1); 
   end

   endfunction

   
   virtual function string get_status_as_string();
      string star = " ";
      svaunit_status_type computed_test_status = get_status();

      if(get_status() == SVAUNIT_FAIL) begin
         star = "*";
      end

      return $sformatf("\n\t%s   %s %s (%0d/%0d SVAUnit checks PASSED)", star, get_test_name(), computed_test_status.name(),
         get_nof_tests() - get_nof_failures(), get_nof_tests());
   endfunction

   
   virtual function string get_status_tests();
      return get_status_as_string();
   endfunction

   
   virtual function string get_checks_for_sva();
      string nice_string = "";

      foreach(lof_checks[check_index]) begin
         nice_string = $sformatf("%s\n\t%s", nice_string, lof_checks[check_index].get_checks_for_sva());
      end

      nice_string = $sformatf("%s", nice_string);
      return nice_string;
   endfunction

   
   virtual function string form_tree(int a_level);
      string extra = "";
      string nice_string = "";

      for(int level_idx = 0; level_idx < a_level; level_idx++) begin
         extra = {"\t", extra};
      end

      nice_string = $sformatf("%s%s%s", nice_string, extra, get_test_name());

      foreach(sequence_name[index]) begin
         extra = "";
         for(int level_idx = 0; level_idx < (a_level + index + 2); level_idx++) begin
            extra = {"\t", extra};
         end

         nice_string = {nice_string, "\n", extra, sequence_name[index]};
      end

      return nice_string;
   endfunction

   
   virtual function void print_sva_info(string a_sva_name);
      vpiw.print_sva_info(a_sva_name);
   endfunction
endclass


/* SLline 66 "../../../UVM/svaunit/sv/svaunit_pkg.sv" 2 */

// Definition of SVAUnit test class which starts a sequence
/* SLline 1 "../../../UVM/svaunit/sv/svaunit_sequence_test.svh" 1 */




class svaunit_sequence_test#(type SEQ_TYPE=svaunit_base_sequence) extends svaunit_test;
   
   
   typedef uvm_component_registry #(svaunit_sequence_test#(SEQ_TYPE)) type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction
 


      SEQ_TYPE seq;

   
   function new(string name="svaunit_sequence_test", uvm_component parent);
      super.new(name, parent);
   endfunction

      virtual function void set_name_for_test();
      update_test_name(seq.get_test_name());
   endfunction

   
   virtual function string form_tree(int a_level);
      string extra = "";

      for(int level_idx = 0; level_idx < a_level; level_idx++) begin
         extra = {"\t", extra};
      end

      return $sformatf("%s%s", extra, seq.form_tree(a_level));
   endfunction

      virtual task test();
      if(!seq.randomize()) begin
         
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_ERROR,"CHECK_SVA_ENABLED_ERR")) 
       uvm_report_error ("CHECK_SVA_ENABLED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg), UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_sequence_test.svh", 63, "", 1); 
   end

      end
      seq.start(sequencer);
   endtask
endclass


/* SLline 69 "../../../UVM/svaunit/sv/svaunit_pkg.sv" 2 */

// Definition of SVAUnit test suite class
/* SLline 1 "../../../UVM/svaunit/sv/svaunit_test_suite.svh" 1 */



class svaunit_test_suite extends svaunit_test;
	
   
   typedef uvm_component_registry #(svaunit_base,"svaunit_base") type_id; 
   static function type_id get_type(); 
     return type_id::get(); 
   endfunction 
   virtual function uvm_object_wrapper get_object_type(); 
     return type_id::get(); 
   endfunction
 
   
   const static string type_name = "svaunit_base"; 
   virtual function string get_type_name (); 
     return type_name; 
   endfunction 
 


		local svaunit_test lof_tests[$];

		bit continue_driving;

	
	function new (string name = "svaunit_test_suite", uvm_component parent);
		super.new(name, parent);

		continue_driving = 1;
	endfunction

	
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);

		set_name_for_test();
	endfunction

	
	virtual function void set_continue_driving(bit a_continue_driving);
		continue_driving = a_continue_driving;
	endfunction

	
	virtual function bit get_continue_driving();
		return continue_driving;
	endfunction

	
	virtual function string create_test_name(string a_test_or_seq_type);
		int index[$];

		index = lof_tests.find_index() with (vpiw.find(item.get_test_name(), a_test_or_seq_type) != -1);

		if(index.size() > 0) begin
			return $sformatf("%s@%0d", a_test_or_seq_type, index.size());
		end else begin
			return a_test_or_seq_type;
		end
	endfunction

	
	virtual function void add_test (uvm_object a_obj);
		svaunit_base_sequence a_seq;
		svaunit_test a_test;
		uvm_component parent;
		string new_name = "";

		if ($cast(a_seq, a_obj)) begin

			automatic svaunit_sequence_test#(svaunit_base_sequence) the_test = svaunit_sequence_test#(svaunit_base_sequence
			)::type_id::create(create_test_name(a_seq.get_type_name()), this);


			if(!($cast(the_test.seq, a_seq))) begin
				
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_FATAL,"SVAUNIT_VPI_WRAPPER_NO_VIF_ERR")) 
       uvm_report_fatal ("SVAUNIT_VPI_WRAPPER_NO_VIF_ERR", 
            "SVAUnit VPI interface for vpi_wrapper class is not set! Please enable SVAUnit package!", UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_test_suite.svh", 99, "", 1); 
   end

			end

			parent = the_test.get_parent();
			new_name = {new_name, parent.get_type_name(), ".", a_seq.get_type_name()};
			the_test.update_test_name(create_test_name(new_name));
			the_test.stop_test = a_seq.get_stop();
			lof_tests.push_back(the_test);
		end
		if ($cast(a_test, a_obj)) begin
			a_test.set_name_for_test();
			lof_tests.push_back(a_test);
		end
	endfunction

		virtual function void update_status();
		int unsigned nof_tests_not_run = 0;

		foreach(lof_tests[test_index]) begin
			lof_tests[test_index].update_status();
		end

		set_nof_tests(get_nof_tests());
		set_nof_failures(get_nof_tests_failed());
		nof_tests_not_run = get_nof_tests_did_not_run();

		set_status(compute_status(get_nof_tests(), get_nof_tests_failed()));
	endfunction

		
	virtual function void get_ran_tests(ref svaunit_test a_tests_ran[$]);
		foreach(lof_tests[test_index]) begin
			if(lof_tests[test_index].started()) begin
				a_tests_ran.push_back(lof_tests[test_index]);
			end
		end
	endfunction

	
	virtual function void get_did_not_run_tests(ref svaunit_test a_tests_ran[$]);
		foreach(lof_tests[test_index]) begin
			if(!(lof_tests[test_index].started())) begin
				a_tests_ran.push_back(lof_tests[test_index]);
			end
		end
	endfunction

	
	virtual function int unsigned get_nof_tests();
		return lof_tests.size();
	endfunction

	
	virtual function int unsigned get_nof_tests_failed();
		int unsigned nof_tests_failed = 0;

		foreach(lof_tests[test_index]) begin
			if(lof_tests[test_index].get_status() == SVAUNIT_FAIL) begin
				nof_tests_failed = nof_tests_failed + 1;
			end
		end

		return nof_tests_failed;
	endfunction

	
	virtual function int unsigned get_nof_tests_did_not_run();
		int unsigned nof_tests_did_not_run = 0;

		foreach(lof_tests[test_index]) begin
			if(lof_tests[test_index].get_status() == SVAUNIT_DID_NOT_RUN) begin
				nof_tests_did_not_run = nof_tests_did_not_run + 1;
			end
		end

		return nof_tests_did_not_run;
	endfunction

	
	virtual function int unsigned get_nof_active_tests();
				svaunit_test tests_ran[$];

				int unsigned nof_active_tests;

				get_ran_tests(tests_ran);
		nof_active_tests = tests_ran.size();
		tests_ran.delete();

		return nof_active_tests;
	endfunction

	
	virtual function string get_tests_names();
				string test_names = "";

				foreach(lof_tests[test_index]) begin
			test_names = $sformatf("%s\n\t%s", test_names, lof_tests[test_index].get_test_name());
		end

		return test_names;
	endfunction

	
	virtual function string get_tests_names_ran();
				string test_names = "";

				svaunit_test tests_ran[$];
		get_ran_tests(tests_ran);

				foreach(tests_ran[test_index]) begin
			test_names = $sformatf("%s\n\t\t%s", test_names, tests_ran[test_index].get_test_name());
		end
		tests_ran.delete();

		return test_names;
	endfunction

	
	virtual function string get_tests_names_did_not_run();
				string test_names = "";

				svaunit_test tests_ran[$];
		get_did_not_run_tests(tests_ran);

				foreach(tests_ran[test_index]) begin
			test_names = $sformatf("%s\n\t\t%s", test_names, tests_ran[test_index].get_test_name());
		end
		tests_ran.delete();

		return test_names;
	endfunction
	
		
	virtual function int unsigned get_total_nof_tested_sva();
				int unsigned nof_tested_sva = 0;

		foreach(lof_tests[test_index]) begin
						nof_tested_sva = nof_tested_sva + lof_tests[test_index].get_nof_tested_sva();
		end

		return nof_tested_sva;
	endfunction

	
	virtual function void get_sva_tested_names(ref string a_tested_sva_names[$]);
		foreach(lof_tests[test_index]) begin
			lof_tests[test_index].get_sva_tested_names(a_tested_sva_names);
		end
	endfunction

	
	virtual function void get_sva_not_tested_names(ref string a_sva_not_tested[$]);
				string tested_sva_names[$];

				string not_tested_sva_names[$];

		int not_tested_index[$];
		int n_tested_index[$];

		foreach(lof_tests[test_index]) begin
			lof_tests[test_index].get_sva_not_tested_names(not_tested_sva_names);
		end

				get_sva_tested_names(tested_sva_names);

		foreach(not_tested_sva_names[sva_index]) begin
			n_tested_index = tested_sva_names.find_index() with (item == not_tested_sva_names[sva_index]);

			if(n_tested_index.size() == 0) begin
				not_tested_index = a_sva_not_tested.find_index() with
					(item == not_tested_sva_names[sva_index]);

				if(not_tested_index.size() == 0) begin
					a_sva_not_tested.push_back(not_tested_sva_names[sva_index]);
				end
			end
		end
	endfunction
	
		
	virtual function void get_checks(ref svaunit_immediate_assertion_info a_checks[$]);
				foreach(lof_tests[test_index]) begin
			lof_tests[test_index].get_checks(a_checks);
		end
	endfunction
	
			virtual task test();
	endtask

		virtual task pre_run();
		
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_INFO,get_name())) 
       uvm_report_info (get_name(), text, UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_test_suite.svh", 343, "", 1); 
   end

				uvm_test_done.raise_objection(this, "", 1);

				start_test();
	endtask

		virtual task post_run();
		
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_INFO,get_name())) 
       uvm_report_info (get_name(), text, UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_test_suite.svh", 353, "", 1); 
   end

				uvm_test_done.drop_objection(this, "", 1);
	endtask

		virtual task start_ut();
		if(enable == 1) begin
			fork
				begin
										process simulate_ts;
					fork
						begin
							simulate_ts = process::self();
							fork
								begin
																		foreach(lof_tests[test_index]) begin
										if(((stop_test == 0) && (continue_driving == 0)) || (continue_driving == 1)) begin
											lof_tests[test_index].start_test();
											lof_tests[test_index].start_ut();
											stop_test = lof_tests[test_index].get_stop();
										end
									end
								end

								begin
									while(((stop_test == 0) && (continue_driving == 0)) || (continue_driving == 1)) begin
										#1ns;
									end
								end
							join_any
						end
					join
					disable fork;
					simulate_ts.kill();
				end
			join

						update_status();

						get_checks(lof_checks);

						print_report();
		end
	endtask

	
	virtual task run_phase(uvm_phase phase);
				uvm_component parent = get_parent();

				if((!started()) && (parent.get_name() == "")) begin
			if(enable == 1) begin
				pre_run();

								fork
					begin
												process start_ut_p;
						fork
							begin
								start_ut_p = process::self();
								start_ut();
								disable fork;
							end
						join
						start_ut_p.kill();
					end
				join

				create_html_report();
				post_run();
			end
		end
	endtask
	
		
	virtual function string get_status_as_string();
		string nice_string = "";
		string star = " ";
		svaunit_status_type computed_test_status = get_status();

		if(get_status() == SVAUNIT_FAIL) begin
			star = "*";
		end


		nice_string = $sformatf("\n\t%s   %s %s (%0d/%0d test cases PASSED)", star, get_test_name(),
			computed_test_status.name(), get_nof_tests() - get_nof_tests_failed() - get_nof_tests_did_not_run(),
			get_nof_tests());

		return nice_string;
	endfunction

	
	virtual function string get_status_tests();
		string nice_string = "";
		string extra = "";

				uvm_component parent = get_parent();

				if(parent.get_name() != "") begin
			extra = $sformatf("%s::", get_type_name());
		end

		nice_string = $sformatf("\n\n-------------------- %s test suite status --------------------\n", get_test_name());
		nice_string = $sformatf("%s\t%s::%s\n", nice_string, get_type_name(), get_test_name());

		foreach(lof_tests[test_index]) begin
			nice_string = {nice_string, "\t\t  ",  lof_tests[test_index].get_status_tests()};
		end

		return nice_string;
	endfunction

		virtual function void print_status();
		string nice_string = "";
		string star = " ";
		svaunit_status_type computed_test_status = get_status();

		if(get_status() == SVAUNIT_FAIL) begin
			star = "*";
		end

		lof_tests.rsort(item) with (item.get_status() == SVAUNIT_FAIL);

		nice_string = $sformatf("\n\n-------------------- %s test suite: Tests status statistics --------------------\n\n",
			get_test_name());
		nice_string = $sformatf("%s   %s   %s %s (%0d/%0d test cases PASSED)\n", nice_string, star, get_test_name(),
			computed_test_status.name(), get_nof_tests() - get_nof_failures() - get_nof_tests_did_not_run(),
			get_nof_tests());

		foreach(lof_tests[test_index]) begin
			nice_string = $sformatf("%s\t%s", nice_string, lof_tests[test_index].get_status_as_string());
		end

		nice_string = $sformatf("%s\n\n", nice_string);

		
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_INFO,get_name())) 
       uvm_report_info (get_name(), text, UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_test_suite.svh", 509, "", 1); 
   end

	endfunction

		virtual function void print_tests();
				string nice_string = "";

				int unsigned total_nof_tests = get_nof_tests();

				int unsigned nof_active_tests = get_nof_active_tests();

		string not_run_tests = get_tests_names_did_not_run();
		
		nice_string = $sformatf("\n\n-------------------- %s test suite: Ran tests statistics --------------------\n\n", get_test_name());
				nice_string = $sformatf("%s\t%0d/%0d Ran tests",
			nice_string, nof_active_tests, total_nof_tests);
		nice_string = $sformatf("%s\n\t%s\n\n", nice_string, get_tests_names_ran());

		if(not_run_tests != "") begin
			nice_string = $sformatf("\n%s\n\t%0d/%0d Tests did not run during simulation",
				nice_string, total_nof_tests - nof_active_tests, total_nof_tests);
			nice_string = $sformatf("%s\n\t%s\n\n", nice_string, not_run_tests);
		end

		
   begin 
     if (uvm_report_enabled(UVM_NONE,UVM_INFO,get_name())) 
       uvm_report_info (get_name(), text, UVM_NONE, "/home/alain/surelog/UVM/svaunit/sv/svaunit_test_suite.svh", 537, "", 1); 
   end

	endfunction

	
	virtual function string form_tree(int a_level);
		string extra = "";
		string nice_string;

		for(int level_idx = 0; level_idx < a_level; level_idx++) begin
			extra = {"\t", extra};
		end

		if(a_level == 0) begin
			extra = {"\t", extra};
		end
		
		nice_string = {extra, get_test_name()};

		foreach(lof_tests[test_index]) begin
			nice_string = {nice_string, "\n", extra, lof_tests[test_index].form_tree(a_level + 1)};
		end

		return nice_string;
	endfunction
endclass


/* SLline 72 "../../../UVM/svaunit/sv/svaunit_pkg.sv" 2 */

endpackage

