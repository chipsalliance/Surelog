// $Id: //dvt/vtech/dev/main/ovm-tests/examples/basic_examples/pkg/test_urm.sv#1 $
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
module test;
  import ovm_pkg::*;

  class lower extends ovm_component;
    int data;
    string str;

    function new (string name, ovm_component parent);
      super.new(name, parent);
    endfunction

    task run();
      #10 $display("%0t: %s HI", $time, get_full_name());
    endtask

    function string get_type_name();
      return "lower";
    endfunction

    function void post_new();
       void'(get_config_int("data", data));
       void'(get_config_string("str", str));
    endfunction 

    function void do_print(ovm_printer printer);
      printer.print_field(data, 32, "data");
      printer.print_string(str, "str");
    endfunction
  endclass

  class myunit extends ovm_component;
   lower l1;
   lower l2;
   int a[];

    function new (string name, ovm_component parent);
      super.new(name, parent, 0);
      l1 = new ("l1", this);
      l2 = new ("l2", this);
      set_config_string("l1", "str", "hi");
      set_config_int("*", "da*", 'h100);
      l1.data = 'h30;
      l2.data = 'h40;
      a = new[5]; for(int i=0; i<5;++i) a[i] = i*i;
    endfunction

    task run();
      #10 $display("%0t: %s HI", $time, get_full_name());
    endtask

    function string get_type_name();
      return "myunit";
    endfunction

    function void do_print(ovm_printer printer);
      printer.print_generic("a", "int_array", a.size(), "");
      printer.m_scope.down("a", null);
      for(int i=0; i<a.size(); ++i) 
        printer.print_field(a[i], 32, $psprintf("a[%0d]", i), OVM_HEX, "[");
      printer.m_scope.up(null);
    endfunction
      
  endclass


  // Factory registration 

  class lower_wrapper extends ovm_object_wrapper;
    function ovm_component create_component(string name, ovm_component parent);
      lower u;
      u = new(name, parent);
      return u;
    endfunction
    function string get_type_name();
      return "lower";
    endfunction
    static function bit register_me();
      lower_wrapper w; w = new;
      ovm_factory::auto_register(w);
      return 1;
    endfunction
    static bit is_registered = register_me();
  endclass

  class myunit_wrapper extends ovm_object_wrapper;
    function ovm_component create_component(string name, ovm_component parent);
      myunit u;
      u = new(name, parent);
      return u;
    endfunction
    function string get_type_name();
      return "myunit";
    endfunction
    static function bit register_me();
      myunit_wrapper w; w = new;
      ovm_factory::auto_register(w);
      return 1;
    endfunction
    static bit is_registered = register_me();
  endclass

  myunit mu = new("mu", null);

`ifdef INCA
  class mydata extends ovm_object;
    string foo[string];
    `ovm_object_utils_begin(mydata)
      `ovm_field_aa_string_string(foo, OVM_DEFAULT)
    `ovm_object_utils_end
  endclass
`else
  class mydata extends ovm_object;
    function ovm_object create(string name);
      mydata d; d=new; d.set_name(name);
      return d;
    endfunction // ovm_object
  endclass

  class mydata_wrapper extends ovm_object_wrapper;
    function ovm_object create_object(string name="");
      mydata u;
      u = new;
      if(name !="") u.set_name(name);
      return u;
    endfunction
    function string get_type_name();
      return "myobject";
    endfunction
    static function bit register_me();
      mydata_wrapper w; w = new;
      ovm_factory::auto_register(w);
      return 1;
    endfunction
    static bit is_registered = register_me();
  endclass
`endif 

  mydata bar = new;

  initial begin
    set_config_int("mu.*", "data", 101);
    set_config_string("mu.*", "str", "hi");
    set_config_int("mu.l1", "data", 55);
    set_config_object("mu.*", "obj", bar);
    mu.print_config_settings("", null, 1);
  end

  initial begin
    mu.print();
    ovm_factory::print_all_overrides(1);
    run_test();
    mu.print();
  end
  initial
    #5 mu.l1.kill();
endmodule
