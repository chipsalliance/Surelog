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

`include "tb_cfg.sv"
`include "trans.sv"
`include "driver.sv"

class tb_env extends vmm_env;

  tb_cfg            cfg;
  trans_driver      drvr;
  trans_atomic_gen  gens[];
  trans_channel     chans[];

  function new();
    cfg = new();
  endfunction

  virtual function void gen_cfg();
    super.gen_cfg();
    void'(cfg.randomize());
    `vmm_note(log, cfg.psdisplay("CFG:"));
  endfunction

  virtual function void build();
    super.build();

    this.gens  = new [cfg.num_chans];
    this.chans = new [cfg.num_chans];

    foreach (chans[i]) begin
       string id_s;

       id_s = $psprintf("%0d", i);
       this.chans[i] = new({"Chan", id_s}, id_s);
       this.gens[i]  = new({"Gen", id_s}, i, chans[i]);
       this.gens[i].stop_after_n_insts = cfg.num_trans;
    end
    drvr  = new("Drvr", this.chans);
  endfunction

  virtual task start();
    super.start();

    foreach (chans[i]) begin
      start_record_replay(chans[i], i);
    end

    begin
      string match_xactors = (cfg.mode == tb_cfg::PLAYBACK) ? "/Drvr/" : "/./";
      // vmm_xactor_iter object iterating over all the transactors
      `foreach_vmm_xactor(vmm_xactor, "/./", match_xactors) begin
        `vmm_note(log, $psprintf("Starting %s", xact.get_instance()));
        xact.start_xactor();
      end
    end
  endtask

  // if mode is set to RECORD mode, transaction information is 
  // dumped in a file. If mode is set to PLAYBACK mode, transaction 
  // information is loaded from the file.
  virtual task start_record_replay(vmm_channel chan, int i);
     fork begin
          string id_s = $psprintf("%0d", i);
          if (cfg.mode == tb_cfg::RECORD) begin
             void'(chan.record({"Chan", id_s, ".dat"}));
          end
          else if (cfg.mode == tb_cfg::PLAYBACK) begin
             bit success;
             trans tr = new;
             chan.playback(success, {"Chan", id_s, ".dat"}, tr);
             if (!success) begin
                `vmm_error(log, {"Playback mode failed for channel", id_s});
             end
          end
     end
     join_none
  endtask

  virtual task wait_for_end();
    super.wait_for_end();
    if (cfg.mode == tb_cfg::PLAYBACK) begin
      foreach (chans[i])
        chans[i].notify.wait_for(vmm_channel::PLAYBACK_DONE);
    end 
    else
    begin
      //vmm_xactor_iter object iterating over all the generators
      `foreach_vmm_xactor(trans_atomic_gen, "/./", "/./") begin
        xact.notify.wait_for(trans_atomic_gen::DONE);
      end
    end
    #100;
  endtask
endclass

