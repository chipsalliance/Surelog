// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    Copyright 2009 Mentor Graphics Corporation
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


`ifndef VMM_SQL__SV
`define VMM_SQL__SV

`include "vmm.sv"

import "DPI-C" function string vmm_sql_get_hostname_dpi();
import "DPI-C" function string vmm_sql_get_utc_dpi(output int t_sec, output int t_usec, output shortint t_zone);
import "DPI-C" function string vmm_sql_get_envar_dpi(input string envar);
import "DPI-C" function string vmm_sql_get_day_dpi();
import "DPI-C" function string vmm_sql_get_hour_dpi();
import "DPI-C" function string vmm_sql_get_min_dpi();
import "DPI-C" function string vmm_sql_get_month_dpi();
import "DPI-C" function string vmm_sql_get_sec_dpi();
import "DPI-C" function string vmm_sql_get_systime_dpi();
import "DPI-C" function string vmm_sql_get_year_dpi();
import "DPI-C" function void vmm_sql_sys_info_init_dpi();

`include "perf/vmm_sql_db.sv"
`ifdef USE_SQLITE
`include "perf/vmm_sql_db_sqlite.sv"
`else
`include "perf/vmm_sql_db_ascii.sv"
`endif

`endif
