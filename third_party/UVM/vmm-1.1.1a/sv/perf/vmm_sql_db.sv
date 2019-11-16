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


`ifndef VMM_SQL_DB__SV
`define VMM_SQL_DB__SV

typedef class vmm_sql_db;

class vmm_sql_table;
   /*local*/ typedef enum int {PERF_TABLE=0,
                               SYS_TABLE=1,
                               USR_TABLE_DEFAULT=255} datakind_e;
   protected vmm_sql_db db;
   protected string schema;
   protected string schema_data;
   string name;
   byte datakind; 
   

   /*local*/ extern function new(string name,
                                 string schema_data,
                                 vmm_sql_db db,
                                 byte datakind=255);

   extern function string get_tblname();
   extern function vmm_sql_db get_db();
   extern function int insert(string data);

   /*local*/ extern function string Xget_schemaX();
   /*local*/ extern function string Xget_schema_dataX();
endclass: vmm_sql_table

virtual class vmm_sql_db;

   protected vmm_sql_table tables[$];

   // contents of vmm_runs table - consistent across all dbs 
   local static string vmm_runs_table_name;
   local static string vmm_runs_utctime;
   local static string vmm_runs_hostname;
   local static int unsigned vmm_runs_seed;
   local static shortint vmm_runs_t_zone;
   local static int vmm_runs_t_sec;

   // table name expansion variables
   local static string vmm_runs_day;
   local static string vmm_runs_hour;
   local static string vmm_runs_min;
   local static string vmm_runs_month;
   local static string vmm_runs_progname;
   local static string vmm_runs_sec;
   local static string vmm_runs_systime;
   local static string vmm_runs_year;
   
   //singleton control for initialization of table
   local static bit vmm_runs_init = 0;

   // table which contains table lists..
   protected vmm_sql_table tables_table; 

   vmm_log log;

   extern function new();
   extern function string get_dbname();
   extern function string get_info(string format);
   extern function vmm_sql_table get_table(string tablename);
   extern function int get_table_names(output string tablenames[],
                                       input string regexp = "."); 
   extern function vmm_sql_table create_table(string tablename,
                                              string scheme,
                                              byte datakind=255);
   extern virtual function int status();
   extern virtual function int statement(string sql_stmt);
   extern virtual function void commit();
   extern virtual function void close();

   // Return an ID that is unique in the DB
   /*extern*/ pure virtual local function int get_unique_id();

   /*local*/ extern function vmm_sql_table Xcreate_table_baseX(string tablename,
                                              string scheme,
                                              byte datakind=255,
                                              bit add_to_tables=1 );
   /*local*/ extern function void Xcreate_system_tablesX();
   /*local*/ extern function string Xexpand_name_optsX(string instr, 
                                                       string opt);
   /*local*/ extern function string Xexpand_nameX(string regexp);
  
endclass: vmm_sql_db

//------------------------------------------------------------------
//
//  Implementation
//


function vmm_sql_db::new();
  int t_sec, t_usec;
  shortint t_zone; 

  if (!vmm_runs_init) begin
     this.vmm_runs_init = 1;
     this.vmm_runs_hostname = vmm_sql_get_hostname_dpi();
     // FIX: Remove all SQL-illegal characters from hostname
     `foreach_str (this.vmm_runs_hostname,index)
       if (this.vmm_runs_hostname[index] == "-")
         this.vmm_runs_hostname[index] = "_";
     if (!($value$plusargs("ntb_random_seed=%d", this.vmm_runs_seed))) begin
        this.vmm_runs_seed = 1;
     end 
     this.vmm_runs_utctime = vmm_sql_get_utc_dpi(this.vmm_runs_t_sec, t_usec, this.vmm_runs_t_zone); 
     this.vmm_runs_day = vmm_sql_get_day_dpi();
     this.vmm_runs_hour = vmm_sql_get_hour_dpi();
     this.vmm_runs_min = vmm_sql_get_min_dpi();
     this.vmm_runs_month = vmm_sql_get_month_dpi();
     this.vmm_runs_progname = "NYI"; //TODO
     this.vmm_runs_sec = vmm_sql_get_sec_dpi();
     this.vmm_runs_systime = vmm_sql_get_systime_dpi();
     this.vmm_runs_year = vmm_sql_get_year_dpi();
  end
endfunction: new


function string vmm_sql_db::get_dbname();
   return (this.log.get_instance());
endfunction: get_dbname

function string vmm_sql_db::get_info(string format);
   return this.Xexpand_nameX(format);
endfunction: get_info


function vmm_sql_table vmm_sql_db::get_table(string tablename);
   vmm_sql_table tbl[$];
   tbl = this.tables.find( x ) with ( x.name == tablename ); 
   if (tbl.size()) begin
      //Only one table with that name can exist (maximum)
      return ( tbl[0] ); 
   end else begin
      return (null);
   end
endfunction: get_table

function string vmm_sql_db::Xexpand_name_optsX(string instr, 
                                               string opt);
  string pre, post, outstr; 
  outstr = instr; 
  //incase someone uses the same option multiple times.
  while (`vmm_str_match(outstr, opt)) begin
     pre = `vmm_str_prematch(outstr);
     post = `vmm_str_postmatch(outstr);
     case(opt)
	"%D": begin
	   $swrite(outstr, "%s%s%s", pre, this.vmm_runs_day, post);  
	end 
	"%h": begin
	   $swrite(outstr, "%s%s%s", pre, this.vmm_runs_hostname, post);  
	end 
	"%H": begin
	   $swrite(outstr, "%s%s%s", pre, this.vmm_runs_hour, post);  
	end 
	"%m": begin
	   $swrite(outstr, "%s%s%s", pre, this.vmm_runs_min, post);  
	end 
	"%M": begin
	   $swrite(outstr, "%s%s%s", pre, this.vmm_runs_month, post);  
	end 
	"%p": begin
	   $swrite(outstr, "%s%s%s", pre, this.vmm_runs_progname, post);  
	end 
	"%s": begin
	   $swrite(outstr, "%s%0d%s", pre, this.vmm_runs_seed, post);  
	end 
	"%S": begin
	   $swrite(outstr, "%s%s%s", pre, this.vmm_runs_sec, post);  
	end 
	"%t": begin
	   $swrite(outstr, "%s%s%s", pre, this.vmm_runs_systime, post);  
	end 
	"%Y": begin
	   $swrite(outstr, "%s%s%s", pre, this.vmm_runs_year, post);  
	end 
	"%%": begin
	   $swrite(outstr, "%s%%s", pre, post);  
	end 
	"%$": begin
	   $swrite(outstr, "%s$%s", pre, post);  
	end 
     endcase 
  end

  return (outstr);
endfunction: Xexpand_name_optsX

function string vmm_sql_db::Xexpand_nameX(string regexp);
   string dbname;
   string opts[$];

   opts.push_back("%D");
   opts.push_back("%h");
   opts.push_back("%H");
   opts.push_back("%m");
   opts.push_back("%M");
   opts.push_back("%p");
   opts.push_back("%s");
   opts.push_back("%S");
   opts.push_back("%t");
   opts.push_back("%Y");
   opts.push_back("%%");
   opts.push_back("%$");

   dbname = regexp;
   //fix up ${var[=val]} 
   // need to escape $, {, and }. Can do so by placing inside brackets or by
   // using double backslash, e.g. \\{
   while (`vmm_str_match(dbname,"[$][{]([a-zA-Z0-9.+_]*)(=[^}]+)?[}]")) begin
      string envar, enval, pre, post, default_enval;
      pre = `vmm_str_prematch(dbname);
      post = `vmm_str_postmatch(dbname);
      envar = `vmm_str_backref(dbname, 0);
      default_enval = `vmm_str_backref(dbname, 1);
      //remove the leading '=' in the default value
      if (default_enval == "") begin
         default_enval = default_enval.substr(1, default_enval.len() - 1); 
      end
     
      if (envar[0] == "+") begin
         if (!($value$plusargs({envar.substr(1,envar.len()-1),"=%s"}, enval))) begin
            enval = default_enval;
         end
         $swrite(dbname, "%0s%0s%0s", pre, enval, post ); 
      end else begin
         enval = vmm_sql_get_envar_dpi(envar);
         if (enval == "") begin
            enval = default_enval;
         end 
         $swrite(dbname, "%0s%0s%0s", pre, enval, post ); 
      end
   end

   //expand the other options..
   foreach (opts[i]) begin
      dbname = Xexpand_name_optsX(dbname, opts[i]);
   end

   return(dbname);

endfunction: Xexpand_nameX
                                         

function int vmm_sql_db::get_table_names(output string tablenames[],
                                         input  string regexp = "."); 
   string tablename;
   string matched_tables[$];

   //get the list of tables which match this name
   `foreach (this.tables,i) begin 
       string tblname = this.tables[i].get_tblname();
       //return if not a system table and name matches...
       if (`vmm_str_match(tblname, regexp)) begin
          matched_tables.push_back(tblname);
       end
   end 

   //populate the tablenames output with the above tablenames
   `ifdef INCA
    tablenames = new[matched_tables.size()];
    foreach(matched_tables[i]) tablenames[i] = matched_tables[i];
   `else
   tablenames = matched_tables;
   `endif

   return (tablenames.size());
endfunction: get_table_names

function vmm_sql_table vmm_sql_db::Xcreate_table_baseX(string tablename,
                                                string scheme,
                                                byte datakind=255,
                                                bit add_to_tables=1); 
   vmm_sql_table tbl = new(this.Xexpand_nameX(tablename), scheme,
                           this, datakind);
   if (this.statement(tbl.Xget_schemaX())) begin
      tbl = null;
   end
   else begin
      this.tables.push_back(tbl);
   end

   // Create an entry in tables_table with the correct table type
   // only if it is a user table 
   if (add_to_tables && this.tables_table != null) begin
      this.tables_table.insert($psprintf("\"%0s\", %0d", tablename,
                                         $unsigned(datakind)));
   end
   return (tbl);
endfunction: Xcreate_table_baseX

function vmm_sql_table vmm_sql_db::create_table(string tablename,
                                                string scheme,
                                                byte datakind=255); 
   return(Xcreate_table_baseX(tablename, scheme, datakind));
endfunction: create_table


function void vmm_sql_db::Xcreate_system_tablesX();
  vmm_sql_table vmm_runs_table;
  string   vmm_tables;

  vmm_runs_table = this.Xcreate_table_baseX(
                      "vmm_runs",
                      "hostname VARCHAR(255), utime INTEGER, systime VARCHAR(30), tzone SMALLINT, seed INTEGER UNSIGNED, tables VARCHAR(255)",
                      vmm_sql_table::SYS_TABLE,
                      0
                   ); 

  $sformat(vmm_tables, "vmm_run_%s_%0d_%0d_%0d", this.vmm_runs_hostname,
           this.vmm_runs_t_sec, this.vmm_runs_seed, this.get_unique_id());

  void'(vmm_runs_table.insert(
     $psprintf("\"%0s\", %0d, \"%0s\", %d, %0d, \"%0s\"",
               this.vmm_runs_hostname,
               this.vmm_runs_t_sec,
               this.vmm_runs_utctime,
               this.vmm_runs_t_zone,
               this.vmm_runs_seed,
               vmm_tables))); 

  this.tables_table = this.Xcreate_table_baseX(
                         vmm_tables,
                         "tblname VARCHAR(255), datakind TINYINT",
                         vmm_sql_table::SYS_TABLE,
                         0 
                      );

endfunction: Xcreate_system_tablesX

function vmm_sql_table::new(string name,
                            string schema_data,
                            vmm_sql_db db,
                            byte datakind = 255);
   this.db = db;
   this.name = name;
   this.datakind = datakind; 
   this.schema_data = schema_data;
   //create the table creation string from the schema_data
   $swrite(this.schema, "CREATE TABLE IF NOT EXISTS %0s (%0s);",
           this.name,
           this.schema_data); 
          
endfunction: new

function string vmm_sql_table::get_tblname();
   return (this.name);
endfunction: get_tblname

function vmm_sql_db vmm_sql_table::get_db();
   return (this.db); 
endfunction: get_db

function int vmm_sql_table::insert(string data);
   string sql_stmt;
   $swrite(sql_stmt,
           "INSERT INTO %0s VALUES (%0s);",
           this.name,
           data);
   return (this.db.statement(sql_stmt));
endfunction: insert

function string vmm_sql_table::Xget_schemaX();
   return(this.schema);
endfunction: Xget_schemaX

function string vmm_sql_table::Xget_schema_dataX();
   return(this.schema_data);
endfunction: Xget_schema_dataX

function int vmm_sql_db::status();
endfunction: status

function int vmm_sql_db::statement(string sql_stmt);
endfunction: statement

function void vmm_sql_db::commit();
endfunction: commit

function void vmm_sql_db::close();
endfunction: close

`endif
