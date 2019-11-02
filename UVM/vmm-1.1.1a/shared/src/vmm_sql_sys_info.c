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


#ifndef VMM_SQL_SYS_INFO__C
#define VMM_SQL_SYS_INFO__C

#include <stdio.h>
#include <sys/time.h>
#include <time.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <ctype.h>

static char timebuf[30];
static char tzchar[10];
static struct timeval tv;
static time_t curtime;

/* Protos */

/* Get hostname */
char *vmm_sql_get_hostname_dpi()
{
   static char hname[256];
   char *c;

   gethostname(hname, 256);
   hname[255] = '\0'; /* Just in case it was too long */
   if (c = strchr(hname, '.')) {  /* Hostname may be qualified with a domain */
      *c = '\0';                  /* If so, truncate to make valid SQL identifier */
   }
   for (c = hname; *c != '\0'; c++) { /* Make valid identifier */
      if (!isalnum(*c)) *c = '_';
   }

   return(hname);
}

static int vmm_sql_sys_info_init_done = 0;
void vmm_sql_sys_info_init_dpi()
{
   if (vmm_sql_sys_info_init_done) 
      return;

   gettimeofday(&tv, NULL);
   curtime = tv.tv_sec;
   vmm_sql_sys_info_init_done = 1;
}

/* Get UTC time as a string in the format of SQL "yyyymmdd hh:mm:ss"
   and also in the format of sec,usec since Epoch
   Code taken from Mike Chirico's code online */

char *vmm_sql_get_utc_dpi(long *sec, long *usec, short int *tz )
{
   
   vmm_sql_sys_info_init_dpi();
   strftime(timebuf, sizeof(timebuf), "%Y%m%d %T", localtime(&curtime));
   strftime(tzchar, sizeof(tzchar), "%z", localtime(&curtime));
   *tz = atoi(tzchar);
   *usec = tv.tv_usec;
   *sec = tv.tv_sec;
   return(timebuf);
}

char *vmm_sql_get_envar_dpi(const char *envar)
{
   return(getenv(envar));
}

char *vmm_sql_get_day_dpi()
{
   vmm_sql_sys_info_init_dpi();
   strftime(timebuf, sizeof(timebuf), "%d", localtime(&curtime));
   return(timebuf);
}

char *vmm_sql_get_hour_dpi()
{
   vmm_sql_sys_info_init_dpi();
   strftime(timebuf, sizeof(timebuf), "%H", localtime(&curtime));
   return(timebuf);
}

char *vmm_sql_get_min_dpi()
{
   vmm_sql_sys_info_init_dpi();
   strftime(timebuf, sizeof(timebuf), "%M", localtime(&curtime));
   return(timebuf);
}

char *vmm_sql_get_month_dpi()
{
   vmm_sql_sys_info_init_dpi();
   strftime(timebuf, sizeof(timebuf), "%m", localtime(&curtime));
   return(timebuf);
}

char *vmm_sql_get_sec_dpi()
{
   vmm_sql_sys_info_init_dpi();
   strftime(timebuf, sizeof(timebuf), "%S", localtime(&curtime));
   return(timebuf);
}

char *vmm_sql_get_systime_dpi()
{
   vmm_sql_sys_info_init_dpi();
   strftime(timebuf, sizeof(timebuf), "%Y%m%d%H%M%S", localtime(&curtime));
   return(timebuf);
}

char *vmm_sql_get_year_dpi()
{
   vmm_sql_sys_info_init_dpi();
   strftime(timebuf, sizeof(timebuf), "%Y", localtime(&curtime));
   return(timebuf);
}

#endif

#ifdef VMM_SQL_SYS_INFO_SANITY_TEST
int main()
{
   long t_usec, t_sec;
   short int t_zone;
   printf("Time: %s\n", vmm_sql_get_utc_dpi(&t_sec, &t_usec, &t_zone)); 
   printf("Time in sec.usec: %ld.%ld\n", t_sec, t_usec); 
   printf("Time zone       : %0d %s\n", t_zone, tzchar); 
   printf("Hostname: %s\n", vmm_sql_get_hostname_dpi());
   printf("Year: %s\n", vmm_sql_get_year_dpi());
   printf("Month: %s\n", vmm_sql_get_month_dpi());
   printf("Day: %s\n", vmm_sql_get_day_dpi());
   printf("Hour: %s\n", vmm_sql_get_hour_dpi());
   printf("Min: %s\n", vmm_sql_get_min_dpi());
   printf("Sec: %s\n", vmm_sql_get_sec_dpi());
   printf("Systime: %s\n", vmm_sql_get_systime_dpi());
   printf("VCS_HOME: %s\n", vmm_sql_get_envar_dpi("VCS_HOME"));
   
}
#endif

