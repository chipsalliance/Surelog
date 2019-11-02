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

#include <sys/stat.h>



/*************************************************
 * DPI interface function
 * Return a DB-wide unique number
 *************************************************/
int vmm_sqltxt_unique_id_dpi(const char* dbname)
{
    struct stat st;

    if (stat(dbname, &st)) return 0;

    return st.st_size;
}
