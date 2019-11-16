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


`ifndef VMM_SQL_DB_SQLITE__SV 
`define VMM_SQL_DB_SQLITE__SV 

import "DPI-C" function int vmm_sqlite_execute_dpi(string dbname, string sql);  
import "DPI-C" function void vmm_sqlite_close_db_dpi(string dbname);
import "DPI-C" function int vmm_sqlite_create_db_dpi(string dbname);  
import "DPI-C" function int vmm_sqlite_init_dpi(); 
import "DPI-C" function string vmm_sqlite_error_dpi();
import "DPI-C" function int vmm_sqlite_unique_id_dpi(string dbname);  

typedef class vmm_sql_db_sqlite; 

//MUST be a power of 2.
`define VMM_SQLITE_NUM_TRANS_TO_COMMIT 2047
class vmm_sql_db_sqlite extends vmm_sql_db;

   local string dbname;

   local static bit init_done = 0;
   local bit last_failed;
   local static int num_transactions = 0;
`ifndef VMM_SQLITE_TRANSACTION_DISABLE
   local static int num_transactions_before_commit = `VMM_SQLITE_NUM_TRANS_TO_COMMIT;
   local static bit uncommitted = 0;
`endif

   extern function new(string dbname);
   extern virtual function int status();
   extern virtual function int statement(string sql_stmt);
   extern virtual function void commit();
   extern virtual function void close();

   // Return an ID that is unique in the DB
   extern local virtual function int get_unique_id();
endclass: vmm_sql_db_sqlite

//------------------------------------------------------------------
//
//  Implementation
//

function vmm_sql_db_sqlite::new(string dbname);
   super.new();
   this.dbname = Xexpand_nameX(dbname);
   this.last_failed = 0;
   this.log = new("SQLdb", this.dbname);
   if (!init_done) begin
      if (vmm_sqlite_init_dpi()) begin
         `vmm_fatal (this.log, vmm_sqlite_error_dpi());
         this.last_failed = 1;
      end else begin
         init_done = 1;
      end
   end    
   if (vmm_sqlite_create_db_dpi(this.dbname)) begin
      `vmm_error (this.log, vmm_sqlite_error_dpi());
      this.last_failed = 1;
   end else begin
      Xcreate_system_tablesX();
   end
endfunction: new

function int vmm_sql_db_sqlite::status();
   return(this.last_failed);
endfunction: status

function int vmm_sql_db_sqlite::statement(string sql_stmt);
`ifndef VMM_SQLITE_TRANSACTION_DISABLE
   int num_transactions_modulo = num_transactions & num_transactions_before_commit;
   if ((num_transactions_modulo == 0) && (this.uncommitted == 0)) begin
      vmm_sqlite_execute_dpi(this.log.get_instance(), "BEGIN TRANSACTION;");
      this.uncommitted = 1;
   end
`endif
   if(vmm_sqlite_execute_dpi(this.log.get_instance(), sql_stmt)) begin
      this.last_failed = 1;
      `vmm_error (this.log, vmm_sqlite_error_dpi());
   end else begin
      this.last_failed = 0;
   end
`ifndef VMM_SQLITE_TRANSACTION_DISABLE
   if (num_transactions_modulo == num_transactions_before_commit) begin
      vmm_sqlite_execute_dpi(this.log.get_instance(), "END TRANSACTION;");
      this.uncommitted = 0;
   end
`endif
   num_transactions++;
   return(this.last_failed);
endfunction: statement

function void vmm_sql_db_sqlite::commit();
`ifndef VMM_SQLITE_TRANSACTION_DISABLE
   if (this.uncommitted) begin
      //commit, and begin a new transaction
      vmm_sqlite_execute_dpi(this.log.get_instance(), "END TRANSACTION;");
      vmm_sqlite_execute_dpi(this.log.get_instance(), "BEGIN TRANSACTION;");
   end
`endif
endfunction: commit

function void vmm_sql_db_sqlite::close();
`ifndef VMM_SQLITE_TRANSACTION_DISABLE
   //if commit has not already happend, commit transaction before closing. 
   if (this.uncommitted) begin
      vmm_sqlite_execute_dpi(this.log.get_instance(), "END TRANSACTION;");
      this.uncommitted = 0;
   end
`endif
   vmm_sqlite_close_db_dpi(this.log.get_instance());
endfunction: close


function int vmm_sql_db_sqlite::get_unique_id();
   // Need to return a unique ID from the DB.
   // like the number of rows in the vmm_runs table...
   return vmm_sqlite_unique_id_dpi(this.dbname);
endfunction: get_unique_id

`endif
