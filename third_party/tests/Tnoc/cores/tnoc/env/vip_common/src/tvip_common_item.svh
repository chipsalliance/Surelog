//------------------------------------------------------------------------------
//  Copyright 2017 Taichi Ishitani
//
//  Licensed under the Apache License, Version 2.0 (the "License");
//  you may not use this file except in compliance with the License.
//  You may obtain a copy of the License at
//
//  http://www.apache.org/licenses/LICENSE-2.0
//
//  Unless required by applicable law or agreed to in writing, software
//  distributed under the License is distributed on an "AS IS" BASIS,
//  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//  See the License for the specific language governing permissions and
//  limitations under the License.
//------------------------------------------------------------------------------
`ifndef TVIP_COMMON_ITEM_SVH
`define TVIP_COMMON_ITEM_SVH
class tvip_common_item #(
  type  CONFIGURATION = tue_configuration_dummy,
  type  STATUS        = tue_status_dummy
) extends tue_sequence_item #(CONFIGURATION, STATUS);
  rand  int ipg;

  constraint c_valid_ipg {
    ipg >= -1;
  }

  constraint c_default_ipg {
    soft ipg == -1;
  }

  function int get_ipg();
    return (ipg >= 0) ? ipg : 0;
  endfunction

  `tue_object_default_constructor(tvip_common_item)
endclass
`endif
