
/*********************************************************************************
Copyright (c) 2021 Wavious LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*********************************************************************************/

// Word Address 0x00000000 : WAV_MCUTOP_RSVD (RW)
`define WAV_MCUTOP_RSVD_RSVD_FIELD 31:0
`define WAV_MCUTOP_RSVD_RSVD_FIELD_WIDTH 32
`define WAV_MCUTOP_RSVD_RANGE 31:0
`define WAV_MCUTOP_RSVD_WIDTH 32
`define WAV_MCUTOP_RSVD_ADR 32'h00000000
`define WAV_MCUTOP_RSVD_POR 32'h00000000
`define WAV_MCUTOP_RSVD_MSK 32'hFFFFFFFF

// Word Address 0x00000004 : WAV_MCUTOP_CFG (RW)
`define WAV_MCUTOP_CFG_DEBUG_EN_FIELD 1
`define WAV_MCUTOP_CFG_DEBUG_EN_FIELD_WIDTH 1
`define WAV_MCUTOP_CFG_FETCH_EN_FIELD 0
`define WAV_MCUTOP_CFG_FETCH_EN_FIELD_WIDTH 1
`define WAV_MCUTOP_CFG_RANGE 1:0
`define WAV_MCUTOP_CFG_WIDTH 2
`define WAV_MCUTOP_CFG_ADR 32'h00000004
`define WAV_MCUTOP_CFG_POR 32'h00000000
`define WAV_MCUTOP_CFG_MSK 32'h00000003

// Word Address 0x00000008 : WAV_MCUTOP_STA (R)
`define WAV_MCUTOP_STA_RESERVED_FIELD 31:0
`define WAV_MCUTOP_STA_RESERVED_FIELD_WIDTH 32
`define WAV_MCUTOP_STA_RANGE 31:0
`define WAV_MCUTOP_STA_WIDTH 32
`define WAV_MCUTOP_STA_ADR 32'h00000008
`define WAV_MCUTOP_STA_POR 32'h00000000
`define WAV_MCUTOP_STA_MSK 32'hFFFFFFFF
