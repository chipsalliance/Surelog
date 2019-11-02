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


`timescale 1ns/1ns

`include "mii.sv"

program p;

`include "mii_env.sv"

class mac_env extends mii_env;
   eth_mac_cfg mac_cfg;

   eth_mac mac_side;
   eth_mac phy_side;
   eth_mac_monitor mac_mon;

   event check_frame;

   function new();
      super.new();
      this.mac_cfg = new;
      // MII checker only supports half-duplex mode
      this.cfg.full_duplex = 0;
      this.cfg.full_duplex.rand_mode(0);
   endfunction: new


   virtual function void gen_cfg();
      bit ok;
      super.gen_cfg();

      ok = this.mac_cfg.randomize() with { rate == ((cfg.is_10Mb) ? 10 : 100);
                                           full_duplex == cfg.full_duplex;
                                           promiscuous == 1; };
      if (!ok) begin
         `vmm_fatal(this.log, "Unable to randomize MAC configuration");
      end
   endfunction: gen_cfg


   virtual function void build();
      super.build();

      this.mac_side = new("MAC Side", 0, this.mac_cfg, null, null,
                          this.mac.tx_chan, this.mac.rx_chan, this.mac.indications);
      this.phy_side = new("PHY Side", 1, this.mac_cfg, null, null,
                          this.phy.tx_chan, this.phy.rx_chan, this.phy.indications);
      this.mac_mon = new("Passive", 2, this.mac_cfg, null, null,
                         this.mon.to_phy_chan, this.mon.to_mac_chan, this.mon.indications);

      // Connect the generators to the MAC layer transactors
      this.mac_src.out_chan = this.mac_side.tx_chan;
      this.phy_src.out_chan = this.phy_side.tx_chan;

      // Reset any verbosity directives that may be lingering in the mii_env...
      this.mac.log.set_verbosity(vmm_log::NORMAL_SEV , "/./", "/./");

//      this.mac.log.set_verbosity(vmm_log::DEBUG_SEV );
      this.mac_side.log.set_verbosity(vmm_log::DEBUG_SEV );
//      this.phy.log.set_verbosity(vmm_log::DEBUG_SEV );
      this.phy_side.log.set_verbosity(vmm_log::DEBUG_SEV );
//      this.mac_mon.log.set_verbosity(vmm_log::DEBUG_SEV );

      `vmm_note(this.log, $psprintf("Verifying %0s-duplex mode at %0dMb/s...",
                                    (this.mac_cfg.full_duplex) ? "full" : "half",
                                    this.mac_cfg.rate));
   endfunction: build
     

   virtual task start();
      super.start();

      this.mac_side.start_xactor();
      this.phy_side.start_xactor();
      this.mac_mon.start_xactor();
   endtask: start

   virtual task wait_for_end();
      super.wait_for_end();
   endtask: wait_for_end

   virtual task check_response();
      fork
         check_stream("Mac->Phy: ", this.phy_side.rx_chan, this.mac_to_phy);
         check_stream("Phy->Mac: ", this.mac_side.rx_chan, this.phy_to_mac);
         check_stream("Phy->Mac(mon): ", this.mac_mon.to_mac_chan, this.phy_to_mon_mac);
         check_stream("Mac->Phy(mon): ", this.mac_mon.to_phy_chan, this.mac_to_mon_phy);
      join
   endtask
endclass


mac_env env = new;

initial
begin
   env.run();
end

endprogram
