// $Id: //dvt/vtech/dev/main/ovm-tests/examples/basic_examples/module/test.sv#1 $
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
package user_pkg;

import ovm_pkg::*;
`include "ovm_macros.svh"

//----------------------------------------------------------------------
// lower
//----------------------------------------------------------------------
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

  function void build();
     void'(get_config_int("data", data));
     void'(get_config_string("str", str));
  endfunction 

  function void do_print(ovm_printer printer);
    printer.print_field("data", data, 32);
    printer.print_string("str", str);
  endfunction
endclass

//----------------------------------------------------------------------
// myunit
//----------------------------------------------------------------------
class myunit extends ovm_component;
  lower l1;
  lower l2;
  int a[];

  function new (string name, ovm_component parent);
    super.new(name, parent);
    set_config_string("l1", "str", "hi");
    set_config_int("*", "da*", 'h100);
    l1 = new ("l1", this);
    l2 = new ("l2", this);
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
    printer.print_array_header("a", a.size());
    for(int i=0; i<a.size(); ++i) 
      printer.print_field( $psprintf("a[%0d]", i), a[i], 32, OVM_HEX, "[");
    printer.print_array_footer();
  endfunction
    
endclass


//----------------------------------------------------------------------
// mydata
//
// in Questa, factory registration is done through explicit
// instantiation of objects and wrappers rather than
// through the macros. However, the ovm_object_registry macro
// will work for both IUS and Questa.
//----------------------------------------------------------------------

class mydata extends ovm_object;
  `ovm_object_registry(mydata,"mydata")
  function ovm_object create(string name);
    mydata d; d=new; d.set_name(name);
    return d;
  endfunction
  virtual function string get_type_name();
    return "mydata";
  endfunction
endclass

endpackage:user_pkg

//----------------------------------------------------------------------
// top
//----------------------------------------------------------------------
module top;
  import ovm_pkg::*;
  import user_pkg::*;

  myunit mu = new("mu", null);
  mydata bar = new;

  initial begin
    set_config_int("mu.*", "data", 101);
    set_config_string("mu.*", "str", "hi");
    set_config_int("mu.l1", "data", 55);
    set_config_object("mu.*", "obj", bar);
    ovm_default_printer.knobs.reference=0;
    mu.print_config_settings("", null, 1);
    mu.print();
    factory.print(1);
    run_test();
    mu.print();
  end

  initial #100 ovm_top.stop_request();

endmodule
