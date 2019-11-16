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


`ifndef MII_SV
`define MII_SV

`include "vmm.sv"

// Example 4-1
`include "mii_if.sv"

// Example 4-32
`include "ethernet.sv"

// Example 4-50
`ifdef VIP_IN_PACKAGE
package mii;
`endif

// Example 4-49
`ifdef VIP_IN_ANONYMOUS_PROGRAM
program;
`endif

// Example 4-48
// Example 4-53
class mii_cfg;
   rand bit is_10Mb;
   rand bit full_duplex;
endclass: mii_cfg


`include "mii_mac.sv"
// Example 4-32
`include "mii_phy.sv"
`include "mii_mon.sv"

// mii / mac SVA checker and external error types
`ifdef SVA_CHECKERS
`include "mii_sva_types.sv"
`include "mii_sva_checker.sv"
`endif

`ifdef VIP_IN_ANONYMOUS_PROGRAM
endprogram
`endif

`ifdef VIP_IN_PACKAGE
endpackage: mii
`endif

`include "mii_mac_bfm.sv"

`endif
