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


class wb_cfg;
   typedef enum {BYTE, WORD, DWORD, QWORD} sizes_e;
   rand sizes_e port_size;
   rand sizes_e granularity;

   typedef enum {CLASSIC, REGISTERED} cycle_types_e;
   rand cycle_types_e cycles;

   rand integer max_n_wss;

   constraint wb_cfg_valid {
      granularity <= port_size;
      max_n_wss >= 0;
   }

   constraint reasonable_max_n_wss {
      max_n_wss == 10;
   }

   constraint supported {
      port_size   == DWORD;
      granularity == BYTE; 
      cycles      == CLASSIC;
   }

   constraint tc1;
   constraint tc2;
   constraint tc3;

   function void display(string prefix = "");
      $write("%s\n", this.psdisplay(prefix));
   endfunction: display

   virtual function string psdisplay(string prefix = "");
      $sformat(psdisplay, "%0s%0s %0s size, %0s granularity. Max WSS=%0d",
               prefix, this.cycles.name(), this.port_size.name(), this.granularity.name(),
               this.max_n_wss);
   endfunction: psdisplay
endclass: wb_cfg


class wb_slave_cfg extends wb_cfg;
   rand bit [63:0] min_addr;
   rand bit [63:0] max_addr;

   constraint wb_slave_cfg_valid {
      max_addr >= min_addr;

   }

   virtual function string psdisplay(string prefix = "");
      $sformat(psdisplay, "%0s at [%h:%h]",
               super.psdisplay(prefix), this.min_addr, this.max_addr);
   endfunction: psdisplay
endclass: wb_slave_cfg
