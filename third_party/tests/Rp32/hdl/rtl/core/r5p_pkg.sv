////////////////////////////////////////////////////////////////////////////////
// R5P: package
////////////////////////////////////////////////////////////////////////////////
// Copyright 2022 Iztok Jeras
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
///////////////////////////////////////////////////////////////////////////////

package r5p_pkg;

// Hardware Performance Monitor events
typedef struct packed {
  logic div_wait;    // 12 - divide delay
  logic mul_wait;    // 11 - multiply delay
  logic taken;       // 10 - branch taken
  logic branch;      // 09 - branch
  logic jump;        // 08 - unconditional jump
  logic store;       // 07 - store operation
  logic load;        // 06 - load operation
  logic if_wait;     // 05 - instruction fetch delay (instruction cache/memory access wait cycle)
  logic ls_wait;     // 04 - load/store delay (cache/memory/periphery access wait cycle)
  logic compressed;  // 03 - compressed instruction retire
  logic instret;     // 02 - instruction retire
  logic reserved;    // 01 - reserved (similar to gap between CSR mcycle and instret)
  logic cycle;       // 00 - clock cycle
} r5p_hpmevent_t;

endpackage: r5p_pkg