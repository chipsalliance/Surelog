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


`ifndef VMM_SQL_DB_ASCII__SV
`define VMM_SQL_DB_ASCII__SV


class vmm_sql_db_ascii extends vmm_sql_db;

   local bit last_failed;
   local int fp; 
   
   extern function new(string dbname,
                       bit    append = 0);
   extern virtual function int status();
   extern virtual function int statement(string sql_stmt);
   extern virtual function void close();

   // Return an ID that is unique in the DB
   extern local virtual function int get_unique_id();
endclass: vmm_sql_db_ascii

//------------------------------------------------------------------
//
//  Implementation
//

function vmm_sql_db_ascii::new(string dbname,
                               bit    append = 0);
   string expanded_name;

   super.new();

   expanded_name = Xexpand_nameX(dbname);
   this.last_failed = 0;
   this.log = new("SQLdb", expanded_name);
   this.fp = $fopen(expanded_name, (append) ? "a" : "w");
   if (!this.fp) begin
      `vmm_error(this.log, {"Unable to open ", expanded_name, " for writing."});
      this.last_failed = 1;
   end else begin
      Xcreate_system_tablesX();
   end
endfunction: new

function int vmm_sql_db_ascii::status();
   return(this.last_failed);
endfunction: status

function int vmm_sql_db_ascii::statement(string sql_stmt);
   if (!this.fp) begin
      `vmm_error(this.log, 
                 {"File ", 
                  this.log.get_instance(), 
                  " not open for writing."});
      this.last_failed = 1;
   end else begin
      $fwrite(this.fp, "%s\n", sql_stmt); 
      this.last_failed = 0;
   end 
   return(this.last_failed);
endfunction: statement

function void vmm_sql_db_ascii::close();
   $fclose(this.fp);
endfunction: close


function int vmm_sql_db_ascii::get_unique_id();
   return $ftell(this.fp);
endfunction: get_unique_id

`endif
