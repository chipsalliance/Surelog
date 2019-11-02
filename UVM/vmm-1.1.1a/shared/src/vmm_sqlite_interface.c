/*
** -------------------------------------------------------------
**    Copyright 2004-2008 Synopsys, Inc.
**    All Rights Reserved Worldwide
** 
**    Licensed under the Apache License, Version 2.0 (the
**    "License"); you may not use this file except in
**    compliance with the License.  You may obtain a copy of
**    the License at
** 
**        http://www.apache.org/licenses/LICENSE-2.0
** 
**    Unless required by applicable law or agreed to in
**    writing, software distributed under the License is
**    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
**    CONDITIONS OF ANY KIND, either express or implied.  See
**    the License for the specific language governing
**    permissions and limitations under the License.
** -------------------------------------------------------------
*/

#include "vmm_sql_sys_info.c"


#define VMM_SQL_DEBUG 0
#define VMM_SQL_DYNLOAD 1

#include <stdio.h>
#include <dlfcn.h>
#include <malloc.h>
#include <string.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include "sqlite3.h"

/**************************************************************/
/* User defined types */
/**************************************************************/
typedef enum {VMM_SQL_PASS = 0,  VMM_SQL_FAIL} vmm_sqlite_status_e;
typedef struct vmm_sqlite_db_entry_s {
   char *name;
   sqlite3* db;
   struct vmm_sqlite_db_entry_s *next;
} vmm_sqlite_db_entry_t;


/**************************************************************/
/* Protos */
/**************************************************************/
vmm_sqlite_status_e vmm_sqlite_execute(sqlite3 *db, const char *stmt);
vmm_sqlite_status_e vmm_sqlite_dynload_get_function(void **p, const char* fn);
vmm_sqlite_status_e vmm_sqlite_dynload_sqlib();
void vmm_sqlite_delete_db(const char *name);
sqlite3* vmm_sqlite_get_db(const char *name);
vmm_sqlite_status_e vmm_sqlite_add_db(const char *name);
int vmm_sqlite_file_exists(const char *filename);

/**************************************************************/
/* Globals */
/**************************************************************/
char vmm_sqlite_err_str[100] = "";
struct {
   vmm_sqlite_db_entry_t *entry;
} vmm_sqlite_db_q = { NULL };

sqlite3 *db;
void *sqlib_handle;

int (*sqlite3_open_p) (
  const char *filename,   /* Database filename (UTF-8) */
  sqlite3 **ppDb          /* OUT: SQLite db handle */
);
int (*sqlite3_close_p) (
  sqlite3 *
);
const char * (*sqlite3_errmsg_p)(
  sqlite3*
);
void (*sqlite3_free_p) (
  void*
);
int (*sqlite3_exec_p) (
  sqlite3*,                     /* An open database */
  const char *sql,              /* SQL to be executed */
  sqlite3_callback,             /* Callback function */
  void *,                       /* 1st argument to callback function */
  char **errmsg                 /* Error msg written here */
);
int (*sqlite3_complete_p) (
  const char *sql
);

/*************************************************
 * DPI interface function
 * Execute an sql statement on an OPEN database. 
 * Return 0 on Success 
 *************************************************/
int vmm_sqlite_execute_dpi(const char *dbname, const char * sql_stmt)
{
#if VMM_SQL_DEBUG
   printf("*DEBUG* SQL cmd %s\n", sql_stmt);
#endif /* VMM_SQL_DEBUG */
   if(vmm_sqlite_execute( vmm_sqlite_get_db(dbname), sql_stmt) == VMM_SQL_FAIL)
   {
      return(1);
   }
   return(0);
}

/*************************************************
 * DPI interface function
 * Closes an SQL database, indexed by name, and 
 *   removes from the active database list.
 *************************************************/
void vmm_sqlite_close_db_dpi(const char* dbname)
{
   vmm_sqlite_delete_db(dbname);
}


/*************************************************
 * DPI interface function
 * Create a SQLite database with a name
 * Return 0 on success
 *************************************************/
int vmm_sqlite_create_db_dpi(const char* dbname)
{
   
   if (vmm_sqlite_add_db(dbname) == VMM_SQL_FAIL) 
   {
      return(1);
   }
   else
   {
      return(0);
   }
}

/*************************************************
 * DPI interface function
 * Initialize / load the dynamic library.
 * Return 0 on success 
 *************************************************/
static int vmm_sqlite_lib_loaded = 0;
int vmm_sqlite_init_dpi()
{
   if (!vmm_sqlite_lib_loaded)
   {
      if (vmm_sqlite_dynload_sqlib() == VMM_SQL_FAIL) 
      {
         return(1);
      }
      vmm_sqlite_lib_loaded = 1;
   }
   return(0);
}

/*************************************************
 * DPI interface function
 * Return the last error message.
 *    may be garbage is the last operation was a
 *    success, so caller must test operation failure 
 *    before using.  
 *************************************************/
char *vmm_sqlite_error_dpi()
{
   return(vmm_sqlite_err_str);
}


/*************************************************
 * DPI interface function
 * Return a DB-wide unique number
 *************************************************/
int vmm_sqlite_unique_id_dpi(const char* dbname)
{
    struct stat st;

    if (stat(dbname, &st)) return 0;

    return st.st_size;
}


/*************************************************
 * Dynamical loading of SQLITE shared library 
 * Return VMM_SQL_PASS on success
 *************************************************/
vmm_sqlite_status_e vmm_sqlite_dynload_sqlib()
{
   const char *lib_err_msg;
   const char *sqlite3_libname = "libsqlite3.so"; 
   char *sqlite3_home_path;
   char sqlite3_lib[300];
   vmm_sqlite_status_e errint;

#if VMM_SQL_DEBUG
   printf("***** SQLITE3_HOME: %s *****\n", getenv("SQLITE3_HOME"));
   printf("***** LD_LIBRARY_PATH: %s *****\n", getenv("LD_LIBRARY_PATH"));
#endif /* VMM_SQL_DEBUG */
#if VMM_SQL_DYNLOAD
   /* Check if SQLITE3_HOME is defined, if so, load from "SQLITE3_HOME/bin/.." */
   if (sqlite3_home_path = getenv("SQLITE3_HOME")) 
   {
      sprintf(sqlite3_lib, "%s/bin/%s", sqlite3_home_path, sqlite3_libname);
      sqlib_handle = dlopen(sqlite3_lib, RTLD_NOW);
      if (!sqlib_handle) {
        sprintf(sqlite3_lib, "%s/lib/%s", sqlite3_home_path, sqlite3_libname);
        sqlib_handle = dlopen(sqlite3_lib, RTLD_NOW);
        if (!sqlib_handle) {
          sprintf(sqlite3_lib, "%s/%s", sqlite3_home_path, sqlite3_libname);
          sqlib_handle = dlopen(sqlite3_lib, RTLD_NOW);
        }
      }
#if VMM_SQL_DEBUG
      printf("***** Library loaded from SQLITE3_HOME: %s ******", sqlite3_lib);
#endif
   }
   else
   { 
      /* Attempt to load from LD_LIBRARY_PATH */
      sqlib_handle = dlopen(sqlite3_libname, RTLD_NOW);
   }
   if (!sqlib_handle) 
   {
#if VMM_SQL_DEBUG
      fprintf(stderr, "Error during dlopen(): %s\n", dlerror());
#endif /* VMM_SQL_DEBUG */
      sprintf(vmm_sqlite_err_str, 
              "*VMM_SQL_ERROR* during dlopen(): %s\n", 
              dlerror());
      return(VMM_SQL_FAIL);
   } 

   /* get all the pointers required from sqlite3 library */
   errint = vmm_sqlite_dynload_get_function((void **) &sqlite3_open_p,  "sqlite3_open");
   errint = vmm_sqlite_dynload_get_function((void **) &sqlite3_close_p,  "sqlite3_close");
   errint = vmm_sqlite_dynload_get_function((void **) &sqlite3_free_p,  "sqlite3_free");
   errint = vmm_sqlite_dynload_get_function((void **) &sqlite3_exec_p,  "sqlite3_exec");
   errint = vmm_sqlite_dynload_get_function((void **) &sqlite3_errmsg_p,  "sqlite3_errmsg");
   errint = vmm_sqlite_dynload_get_function((void **) &sqlite3_complete_p,  "sqlite3_complete");
#else 
   /* Static linking: just point to the actual functions.. */
   sqlite3_open_p = sqlite3_open;
   sqlite3_close_p = sqlite3_close;
   sqlite3_free_p = sqlite3_free;
   sqlite3_exec_p = sqlite3_exec;
   sqlite3_errmsg_p = sqlite3_errmsg;
   sqlite3_complete_p = sqlite3_complete;
   errint = VMM_SQL_PASS;
#endif /* VMM_SQL_DYNLOAD */

   return (errint);
    
}

/*************************************************
 * get function pointer from library
 * Return VMM_SQL_PASS on success
 *************************************************/
vmm_sqlite_status_e vmm_sqlite_dynload_get_function(void **p, const char* fn)
{
   const char *lib_err_msg;
   *p = dlsym(sqlib_handle, fn);
   lib_err_msg = dlerror();
   if (lib_err_msg)
   {
#if VMM_SQL_DEBUG
      fprintf(stderr, "*ERROR* %s\n", lib_err_msg);
#endif /* VMM_SQL_DEBUG */
      sprintf(vmm_sqlite_err_str, "*VMM_SQL_ERROR* %s\n", lib_err_msg);
      return(VMM_SQL_FAIL);
   }
   return(VMM_SQL_PASS);
}
                             

/*************************************************
 * execute without callbacks
 * Return VMM_SQL_PASS on success
 *************************************************/

vmm_sqlite_status_e vmm_sqlite_execute(sqlite3 *db, const char *stmt)
{ 
   char *errmsg;
   if((db == NULL) ||
      ((*sqlite3_exec_p)(
	 db,
	 stmt,
	 NULL,
	 NULL,
	 &errmsg) != SQLITE_OK)
     )
   {
#if VMM_SQL_DEBUG
      fprintf(stderr, "STMT: %s\n", stmt);
      fprintf(stderr, "   *FATAL* %s\n", errmsg);
#endif /* VMM_SQL_DEBUG */
      sprintf(vmm_sqlite_err_str, "*VMM_SQL_ERROR* %s\n", errmsg);
      (*sqlite3_free_p)(errmsg);
      return(VMM_SQL_FAIL);
   }

   return(VMM_SQL_PASS);
}

/*************************************************
 * add entry to dblist 
 * Return VMM_SQL_PASS on success
 *************************************************/
vmm_sqlite_status_e vmm_sqlite_add_db(const char *name)
{
   vmm_sqlite_db_entry_t *entry;
   sqlite3 *db;

   if ((*sqlite3_open_p)(name, &db) != SQLITE_OK)
   {
#if VMM_SQL_DEBUG
      fprintf(stderr, "*FATAL* Failed to open %s\n", name);
#endif /* VMM_SQL_DEBUG */
      sprintf(vmm_sqlite_err_str, "Failed to open SQLITE db: %s", name);
      return(VMM_SQL_FAIL);
   }

   /* create and add entry at the head of the dblist */
   entry = (vmm_sqlite_db_entry_t *) malloc(sizeof(vmm_sqlite_db_entry_t));
   entry->db = db;
   entry->name = strdup(name);
   entry->next = vmm_sqlite_db_q.entry;
   vmm_sqlite_db_q.entry = entry;

   return(VMM_SQL_PASS);
}

/*************************************************
 * lookup and return a db pointer from db list                
 * NULL if does not exist                                     
 *************************************************/
sqlite3* vmm_sqlite_get_db(const char *name)
{
   vmm_sqlite_db_entry_t *entry;
   for (entry = vmm_sqlite_db_q.entry; entry != NULL; entry = entry->next)
   {
      if (strcmp(name, entry->name) == 0)
      {
         return (entry->db);
      }
   }
   return (NULL);
}

/*************************************************
 * delete entry in dblist 
 *************************************************/
void vmm_sqlite_delete_db(const char *name)
{
   vmm_sqlite_db_entry_t *entry, *last_entry;
   
   last_entry = vmm_sqlite_db_q.entry;
   for (entry = vmm_sqlite_db_q.entry; entry != NULL; entry = entry->next)
   {
      if (strcmp(name, entry->name) == 0)
      {
         last_entry->next = entry->next;
         (*sqlite3_close_p)(entry->db);
         free(entry->name);
         free(entry);
         return;
      }
      last_entry = entry;
   }  
   return;
}

/*************************************************
 * File exists ? Return 1.
 *************************************************/
int vmm_sqlite_file_exists(const char *filename)
{
   if( access (filename, F_OK) == 0) 
   {
      return 1;
   }
   return 0;

}
