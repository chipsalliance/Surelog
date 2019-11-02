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


//
// This file needs to be included at the 'VMM_PRE_INCLUDE' point
//

`ifndef VMM_DATA_BASE
   `define VMM_DATA_BASE        vmm_object
`endif
`ifndef VMM_CHANNEL_BASE
   `define VMM_CHANNEL_BASE     vmm_object
`endif
`ifndef VMM_CONSENSUS_BASE
   `define VMM_CONSENSUS_BASE   vmm_object
`endif
`ifndef VMM_NOTIFY_BASE
   `define VMM_NOTIFY_BASE      vmm_object
`endif
`ifndef VMM_XACTOR_BASE
   `define VMM_XACTOR_BASE      vmm_object
`endif
`ifndef VMM_SUBENV_BASE
   `define VMM_SUBENV_BASE      vmm_object
`endif
`ifndef VMM_ENV_BASE
   `define VMM_ENV_BASE         vmm_object
`endif
`ifndef VMM_TEST_BASE
   `define VMM_TEST_BASE        vmm_object
`endif

`define VMM_OBJECT_SET_PARENT(_child, _parent) \
   _child.set_parent(_parent);
