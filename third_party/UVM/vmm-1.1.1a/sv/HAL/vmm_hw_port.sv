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


`ifdef VMM_HW_XACTOR__SV
`else
`define VMM_HW_XACTOR__SV

typedef class vmm_hw_in_port;
typedef class vmm_hw_out_port;

virtual class vmm_hw_arch;
   vmm_log log = new("vmm_hw_arch", "base class");

   virtual function vmm_hw_in_port create_in_port(virtual vmm_hw_in_if_itf in_if,
                                                  string                   name);
      `vmm_fatal(this.log, "vmm_hw_arch::create_in_port() not overloaded");
      return null;
   endfunction: create_in_port

   virtual function vmm_hw_out_port create_out_port(virtual vmm_hw_out_if_itf out_if,
                                                    string                    name);
      `vmm_fatal(this.log, "vmm_hw_arch::create_out_port() not overloaded");
      return null;
   endfunction: create_out_port

   virtual function string connect_to(string hdl_path,
                                      string name);
      return hdl_path;
   endfunction: connect_to

   virtual function void clk_control(virtual vmm_hw_clock_itf clk,
                                     virtual vmm_hw_clock_control_itf ctl);
   endfunction: clk_control

   virtual function void init_sim();
   endfunction

endclass: vmm_hw_arch


virtual class vmm_hw_in_port;
   vmm_log log = new("vmm_hw_in_port", "base class");

   virtual function bit is_rdy();
      `vmm_fatal(this.log, "vmm_hw_in_port::is_rdy() not overloaded");
   endfunction: is_rdy

   virtual task wait_is_rdy();
      `vmm_fatal(this.log, "vmm_hw_in_port::wait_is_rdy() not overloaded");
   endtask: wait_is_rdy

   virtual task send(bit [`VMM_HW_DATA_WIDTH-1:0]  data);
      `vmm_fatal(this.log, "vmm_hw_in_port::send() not overloaded");
   endtask: send
endclass: vmm_hw_in_port


virtual class vmm_hw_out_port;
   vmm_log log = new("vmm_hw_out_port", "base class");

   virtual function bit is_rdy();
      `vmm_fatal(this.log, "vmm_hw_out_port::is_rdy() not overloaded");
   endfunction: is_rdy

   virtual task wait_is_rdy();
      `vmm_fatal(this.log, "vmm_hw_out_port::wait_is_rdy() not overloaded");
   endtask: wait_is_rdy

   virtual task receive(ref bit [`VMM_HW_DATA_WIDTH-1:0]  data,
                        ref time                          stamp);
      `vmm_fatal(this.log, "vmm_hw_out_port::receive() not overloaded");
   endtask: receive
endclass: vmm_hw_out_port

`endif
