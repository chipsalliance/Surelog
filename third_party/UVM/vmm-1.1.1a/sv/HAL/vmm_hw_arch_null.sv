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


`ifdef VMM_HW_ARCH_NULL__SV
`else
`define VMM_HW_ARCH_NULL__SV

typedef class vmm_hw_arch_null_in_port;
typedef class vmm_hw_arch_null_out_port;

class vmm_hw_arch_null extends vmm_hw_arch;
   virtual function vmm_hw_in_port  create_in_port(virtual vmm_hw_in_if_itf in_if,
                                                   string                   name);
      vmm_hw_arch_null_in_port port = new(in_if);
      return port;
   endfunction: create_in_port

   virtual function vmm_hw_out_port create_out_port(virtual vmm_hw_out_if_itf out_if,
                                                    string                    name);
      vmm_hw_arch_null_out_port port = new(out_if);
      return port;
   endfunction: create_out_port

   virtual function string connect_to(string hdl_path,
                                      string name);
      return super.connect_to(hdl_path, name);
   endfunction: connect_to

   virtual function void clk_control(virtual vmm_hw_clock_itf clk,
                                     virtual vmm_hw_clock_control_itf ctl);
      int n;

      clk.no_pos = 0;
      clk.no_neg = 0;
      ctl.cclk_en = 0;
      ctl.cclk_neg_en = 0;

      n = clk.controller_size();
`ifdef VMM_HW_CLOCK_WHY
      clk.controller.push_back(ctl.path);
      clk.rdy_pos.push_back(1'b1);
      clk.rdy_neg.push_back(1'b1);
`endif

      fork
         automatic int i = n;

         forever begin
`ifdef VMM_HW_CLOCK_WHY
            clk.rdy_pos[i] = 1;
`endif
            wait (ctl.rdy_for_cclk === 1'b0);
`ifdef VMM_HW_CLOCK_WHY
            clk.rdy_pos[i] = ctl.rdy_for_cclk;
`endif
            clk.no_pos++;
            wait (ctl.rdy_for_cclk === 1'b1);
            clk.no_pos--;
         end

         forever begin
`ifdef VMM_HW_CLOCK_WHY
            clk.rdy_neg[i] = 1;
`endif
            wait (ctl.rdy_for_cclk_neg === 1'b0);
`ifdef VMM_HW_CLOCK_WHY
            clk.rdy_neg[i] = ctl.rdy_for_cclk_neg;
`endif
            clk.no_neg++;
            wait (ctl.rdy_for_cclk_neg === 1'b1);
            clk.no_neg--;
         end

         forever begin
            ctl.cclk_en = clk.ck_en;
            @ (clk.ck_en);
         end

         forever begin
            ctl.cclk_neg_en = clk.ckn_en;
            @ (clk.ckn_en);
         end
      join_none
   endfunction: clk_control
endclass: vmm_hw_arch_null


class vmm_hw_arch_null_in_port extends vmm_hw_in_port;
   
   local virtual vmm_hw_in_if_itf itf;

   function new(virtual vmm_hw_in_if_itf itf);
`ifdef INCA
      logic[1027:0] path=itf.path;
      log.set_instance($psprintf("%s",path));
`else
      log.set_instance(string'(itf.path));
`endif

      this.itf = itf;
      this.itf.tx_rdy = 1'b0;
   endfunction: new

   virtual function bit is_rdy();
      return this.itf.rx_rdy;
   endfunction: is_rdy

   virtual task wait_is_rdy();
      `vmm_debug(log, "Waiting for RTL to be ready to receive message...");
      do begin
         @(this.itf.ck);
      end
      while (this.itf.rx_rdy !== 1'b1);
      `vmm_debug(log, "RTL is ready to receive message");
   endtask: wait_is_rdy

   virtual task send(bit [`VMM_HW_DATA_WIDTH-1:0]  data);
      logic [1027:0] msg;
      if (this.itf.in_use) begin
         `vmm_fatal(log, "send() task concurrently activated");
      end
      this.itf.in_use  = 1;
      @(this.itf.ck);
      this.itf.tx_rdy <= 1'b1;
      this.itf.msg    <= data;
      `vmm_debug(log, "Waiting to send message...");
      do begin
         @(this.itf.ck);
      end
      while (this.itf.ck.rx_rdy !== 1'b1);
      this.itf.tx_rdy <= 1'b0;
      this.itf.in_use  = 0;
      msg = this.itf.msg;
      `vmm_debug(log, $psprintf("Sent message 'h%h", msg));
   endtask: send
endclass: vmm_hw_arch_null_in_port


class vmm_hw_arch_null_out_port extends vmm_hw_out_port;
   local virtual vmm_hw_out_if_itf itf;

   function new(virtual vmm_hw_out_if_itf itf);
`ifdef INCA
      logic[1027:0] path=itf.path;
      log.set_instance($psprintf("%s",path));
`else
      log.set_instance(string'(itf.path));
`endif

      this.itf = itf;
      this.itf.rx_rdy = 1'b0;
   endfunction: new

   virtual function bit is_rdy();
      return this.itf.tx_rdy;
   endfunction: is_rdy

   virtual task wait_is_rdy();
      `vmm_debug(log, "Waiting for RTL to be ready to send message...");
      do begin
         @(this.itf.ck);
      end
      while (this.itf.ck.tx_rdy !== 1'b1);
      `vmm_debug(log, "RTL is ready to send message");
   endtask: wait_is_rdy

   virtual task receive(ref bit [`VMM_HW_DATA_WIDTH-1:0] data,
                        ref time                         stamp);
      bit [`VMM_HW_DATA_WIDTH-1:0] debug_data;
      if (this.itf.in_use) begin
         `vmm_fatal(log, "receive() task concurrently activated");
      end
      this.itf.in_use  = 1;
      `vmm_debug(log, "Waiting to receive message...");
      @(this.itf.ck);
      this.itf.rx_rdy <= 1'b1;
      do
         @(this.itf.ck);
      while (this.itf.ck.tx_rdy !== 1'b1);
      this.itf.rx_rdy <= 1'b0;
      this.itf.in_use  = 0;
      data  = this.itf.ck.msg;
      debug_data = data;
      stamp = vmm_hw.stamp;
      `vmm_debug(log, $psprintf("Receive message 'h%h stamped %0d", debug_data, stamp));
   endtask: receive
endclass: vmm_hw_arch_null_out_port

`endif
