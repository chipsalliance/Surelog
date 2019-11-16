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

`include "vmm.sv"

class tb_cfg;

  typedef enum bit [1:0] {NORMAL, RECORD, PLAYBACK} mode_e;

  mode_e   mode = NORMAL;
  int num_chans = 1;
  int num_trans = 10;

  function new();
    vmm_opts opts = new;
    string md;
    md = opts.get_string("MODE", "NORMAL", "Specifies the mode");
    case (md)
      "NORMAL"   : mode = NORMAL;
      "RECORD"   : mode = RECORD;
      "PLAYBACK" : mode = PLAYBACK;
    endcase
    num_trans = opts.get_int("NUM_TRANS", num_trans, "Num Of transactions");
    num_chans = opts.get_int("NUM_CHANS", num_chans, "Num Of Driver channels");
  endfunction

  function string psdisplay(string prefix = "");
    psdisplay = $psprintf("%s %s_MODE: NumOfDriverChannels = %0d, Transactions = %0d", 
                          prefix, mode.name(), num_chans, num_trans);
  endfunction
endclass

