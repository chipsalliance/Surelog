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

`ifndef RVM_RAL__SV
`define RVM_RAL__SV


`ifndef VMM_RAL_ADDR_WIDTH
`define VMM_RAL_ADDR_WIDTH 64
`endif

`ifndef VMM_RAL_DATA_WIDTH
`define VMM_RAL_DATA_WIDTH 64
`endif


`include "RAL/vmm_rw.sv"

`include "RAL/vmm_ral_version.sv"

typedef class vmm_ral_field;
typedef class vmm_ral_vfield;
typedef class vmm_ral_reg;
typedef class vmm_ral_vreg;
typedef class vmm_ral_block;
typedef class vmm_ral_mem;
typedef class vmm_ral_sys;
typedef class vmm_ral_access;

class vmm_ral;
   typedef enum {
      BFM,
      BACKDOOR,
      DEFAULT
   } path_e;

   typedef enum {
      RW,
      RO,
      WO,
      W1,
      RU,
      RC,
      W1C,
      A0,
      A1,
      DC,   // Important that DC be followed by OTHER & USER and none other
      OTHER,
      USER0,
      USER1,
      USER2,
      USER3
   } access_e;

   typedef enum {
      QUIET,
      VERB
   } check_e;

   typedef enum {
      NO_ENDIAN,
      LITTLE_ENDIAN,
      BIG_ENDIAN,
      LITTLE_FIFO,
      BIG_FIFO
   } endianness_e;

   typedef enum {
      HARD,
      SOFT
   } reset_e;

   typedef enum {
      NO_COVERAGE  = 'h0000,
      REG_BITS     = 'h0001,
      ADDR_MAP     = 'h0002,
      FIELD_VALS   = 'h0004,
      ALL_COVERAGE = 'h0007
   } coverage_model_e;
endclass: vmm_ral

   
class vmm_ral_callbacks extends vmm_xactor_callbacks;
endclass: vmm_ral_callbacks


`include "RAL/vmm_ral_field.sv"
`include "RAL/vmm_ral_vfield.sv"
`include "RAL/vmm_ral_backdoor.sv"
`include "RAL/vmm_ral_reg.sv"
`include "RAL/vmm_mam.sv"
`include "RAL/vmm_ral_mem.svh"
`include "RAL/vmm_ral_vreg.sv"
`include "RAL/vmm_ral_mem.sv"
`include "RAL/vmm_ral_block_or_sys.sv"
`include "RAL/vmm_ral_block.sv"
`include "RAL/vmm_ral_sys.sv"
`include "RAL/vmm_ral_access.sv"
`include "RAL/vmm_ral_env.sv"
`include "RAL/vmm_ral_tests.sv"

`endif // RVM_RAL__SV
