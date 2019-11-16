// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    Copyright 2008-2009 Mentor Graphics Corporation
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


//`include "mii.sv" // moved mii_env to inside the program block because of references like top.if0.mac_layer.

typedef class mii_env;
class my_eth_frame_atomic_gen_callbacks extends eth_frame_atomic_gen_callbacks;
   bit is_mac;
   mii_env env;

   function new(mii_env env,
                bit is_mac);
      this.is_mac = is_mac;
      this.env    = env;
   endfunction

   virtual task post_inst_gen(eth_frame_atomic_gen gen,
                              eth_frame            obj,
                              ref bit              drop);
      if (is_mac) begin
         this.env.mac_to_phy.push_back(obj);
         this.env.mac_to_mon_phy.push_back(obj);
      end else begin
         this.env.phy_to_mac.push_back(obj);
         this.env.phy_to_mon_mac.push_back(obj);
      end
   endtask
endclass


class mii_env extends vmm_env;
   mii_cfg cfg;
   eth_frame_atomic_gen mac_src;
   eth_frame_atomic_gen phy_src;
   mii_mac_layer mac;
   mii_phy_layer phy;
   mii_monitor   mon;

   eth_frame phy_to_mac[$];
   eth_frame mac_to_phy[$];
   eth_frame phy_to_mon_mac[$];
   eth_frame mac_to_mon_phy[$];

   event check_frame;

   function new();
      $timeformat(-9, 0, "ns", 1);
      this.cfg = new;
   endfunction: new


   virtual function void gen_cfg();
      bit ok;
      super.gen_cfg();

      ok = this.cfg.randomize() with { is_10Mb == 1; };
      if (!ok) begin
         `vmm_fatal(this.log, "Unable to randomize MII configuration");
      end
   endfunction: gen_cfg


   virtual function void build();
      super.build();

      this.mac     = new("MAC Side", 0, this.cfg, top.if0.mac_layer);
      this.phy     = new("PHY Side", 1, this.cfg, top.if0.phy_layer);
      this.mon     = new("Passive", 1, this.cfg, top.if0.passive);

      this.mac_src = new("MAC Side", 0, this.mac.tx_chan);
      this.phy_src = new("PHY Side", 1, this.phy.tx_chan);

      this.mac_src.stop_after_n_insts = 3;
      this.phy_src.stop_after_n_insts = 3;

      fork
         top.if0.mii_FullDuplex <= this.cfg.full_duplex;
      join_none

      this.mac.log.set_verbosity(vmm_log::DEBUG_SEV );
      this.phy.log.set_verbosity(vmm_log::DEBUG_SEV );
//      this.mon.log.set_verbosity(vmm_log::DEBUG_SEV );

      begin
         my_eth_frame_atomic_gen_callbacks cb;
         cb = new(this, 0);
         this.phy_src.append_callback(cb);
         cb = new(this, 1);
         this.mac_src.append_callback(cb);
      end

      fork
         check_response();
     join_none
   endfunction: build
     

   virtual task start();
      super.start();

      this.mac.start_xactor();
      this.phy.start_xactor();
      this.mon.start_xactor();

      // Make sure the signals are initialized and stable for a while
      repeat (10) @(negedge top.tx_clk);

      this.mac_src.start_xactor();
      this.phy_src.start_xactor();
   endtask: start

   virtual task wait_for_end();
      super.wait_for_end();

      // Wait for the generators to be done
      fork
         this.mac_src.notify.wait_for(eth_frame_atomic_gen::DONE);
         this.phy_src.notify.wait_for(eth_frame_atomic_gen::DONE);
      join

      // Wait for the scoreboards to be empty
      while (this.mac_to_phy.size() > 0 ||
             this.phy_to_mac.size() > 0 ||
             this.mac_to_mon_phy.size() > 0 ||
             this.phy_to_mon_mac.size() > 0) begin
         @check_frame;
      end

   endtask: wait_for_end


   virtual task check_response();
      fork
         check_stream("Mac->Phy", this.phy.rx_chan, this.mac_to_phy);
         check_stream("Phy->Mac", this.mac.rx_chan, this.phy_to_mac);
         check_stream("Phy->Mac(mon)", this.mon.to_mac_chan, this.phy_to_mon_mac);
         check_stream("Mac->Phy(mon)", this.mon.to_phy_chan, this.mac_to_mon_phy);
      join
   endtask


   task check_stream(string            prefix,
                     eth_frame_channel snk,
                     ref eth_frame     exp[$]);
      forever begin
         eth_frame fr, act;
         string diff;

         snk.get(act);
         -> this.check_frame;
         act.display(prefix);
         fr = exp.pop_front();
         
         if (!act.compare(fr, diff)) begin
            `vmm_error(this.log, $psprintf("Unexpected %0s frame: %0s\n%s\n%s",
                                           prefix, diff,
                                           act.psdisplay("   Actual: "),
                                           fr.psdisplay("   Expect: ")));
         end
      end
   endtask
     
endclass
