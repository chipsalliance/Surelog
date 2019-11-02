// $Id: simple_item.sv,v 1.4 2007/12/14 10:18:56 redelman Exp $
//----------------------------------------------------------------------
//   Copyright 2007-2008 Mentor Graphics Corporation
//   Copyright 2007-2008 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Ported to VMM, 2008 by Synopsys, Inc.
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------

`ifndef SIMPLE_ITEM_SV
`define SIMPLE_ITEM_SV

//------------------------------------------------------------------------------
//
// CLASS: simple_item
//
// declaration
//------------------------------------------------------------------------------

class simple_item extends vmm_data;

  rand int unsigned addr;
    constraint c1 { addr < 16'h2000; }
  rand int unsigned data;
    constraint c2 { data < 16'h1000; }

  `vmm_data_member_begin(simple_item)
    `vmm_data_member_scalar(addr, DO_ALL)
    `vmm_data_member_scalar(data, DO_ALL)
  `vmm_data_member_end(simple_item)

endclass : simple_item

`vmm_channel(simple_item)

`endif // SIMPLE_ITEM_SV
