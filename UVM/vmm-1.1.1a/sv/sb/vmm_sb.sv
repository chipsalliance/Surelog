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


`ifndef VMM_SB__SV
`define VMM_SB__SV

`ifndef VMM_SB_DS_IN_STDLIB
`include "vmm.sv"
`else
// If VMM_SB code is supposed to be in vmm package,
// the content of the code should only be parsed when
// vmm package is being parsed(VMM_BEING_PARSED).
`ifndef VMM_BEING_PARSED
`define VMM_SB_SKIP
`endif
`endif

`ifndef VMM_SB_SKIP

`include "sb/vmm_sb_version.sv"
`include "sb/vmm_sb_ds.sv"
`include "sb/vmm_sb_ds_iter.sv"
`include "sb/vmm_sb_ds_stream_iter.sv"

`endif // VMM_SB_SKIP
`endif // VMM_SB__SV
