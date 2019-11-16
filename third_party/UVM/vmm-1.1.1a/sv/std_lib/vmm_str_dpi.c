/* 
** -------------------------------------------------------------
**    Copyright 2004-2008 Synopsys, Inc.
**    Copyright 2009 Mentor Graphics Corporation
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

#ifndef VMM_REGEX_LIBRARY
#define VMM_REGEX_LIBRARY

#include <sys/types.h>
#include <regex.h>
#include <string.h>
#include <malloc.h>
#include <stdio.h> 

#include "svdpi.h"

/* Macros */
#define REGEX_ERRBUFSIZE 256
#define REGEX_MAXMATCHES  9

static int REGEX_PRE = 0;
static int REGEX = 1;
static int REGEX_POST = 2;

/* Globals */
static regex_t preg;
static regmatch_t pmatch[REGEX_MAXMATCHES]; 
static char regex_errbuf[REGEX_ERRBUFSIZE]; 
static char *regex_str_global = NULL;
static char *str_to_match_global = NULL;
static int str_return_size = 0;
static char *str_return = NULL;
static int  last_matched;  /* 1 if last match passed, 0 if failed. */


/* Prototypes */
static char *vmm_match_in_string(regmatch_t vmm_match, 
                                 const char *str_to_match,
                                 int match_type);
static int vmm_regex_build(const char *regex_str) ;
static int vmm_regex_compare(const char *str_to_match);

static int vmm_regex(const char *str_to_match,
                     const char *regex_str) ;

/* exposed functions via DPI */
int vmm_str_match(const char *str_to_match,
                  const char *regex_str) ;
char* vmm_str_prematch();
char* vmm_str_postmatch();
char* vmm_str_backref(int n);

/*
 * return the matched substring: helper function
 *   The string is allocated by the callee.
 */
char *vmm_match_in_string(regmatch_t vmm_match, 
                      const char *str_to_match,
                      int match_type) 
{
   
   int  strtmplen;
   int  strstart;

   if (match_type == REGEX_PRE) {
      strtmplen = (vmm_match.rm_so);
      strstart = 0;
   } else if (match_type == REGEX_POST) {
      strtmplen = (strlen(str_to_match) - vmm_match.rm_eo);
      strstart = vmm_match.rm_eo;
   } else {
      strtmplen = (vmm_match.rm_eo - vmm_match.rm_so);
      strstart = vmm_match.rm_so;
   }

   if (str_return_size < (strtmplen+1)) {
      str_return_size = strtmplen * 2;
      if (str_return != NULL) free(str_return);
      str_return = (char *) malloc((str_return_size) * sizeof(char));
   }
   strncpy(str_return,
           str_to_match+strstart,
           strtmplen);
   str_return[strtmplen] = '\0';

#ifdef DEBUG_REGEX
   printf("vmm_match substring: %s\n",
          str_return);
#endif
   return(str_return);

}

/*
 * Compiles the regex.
 * Assumes memory for regex_str
 *  is allocated by caller.
 * Returns error_id (0 == pass)
 */
int vmm_regex_build(const char *regex_str) 
{
   int error_id;
   regfree(&preg); /* free up any vestigial effects from the last regcomp */
   last_matched = 0;
   error_id = regcomp(&preg,
              regex_str,
              REG_EXTENDED);
   if (error_id != 0) {
     regerror(error_id,
              &preg,
              regex_errbuf,
              REGEX_ERRBUFSIZE); 
     printf("Can not compile regexp %0s: %s\n",regex_str,regex_errbuf);
   }
   return(error_id);
}

/*
 * Assumes memory for str_to_match 
 *  is allocated by caller.
 * To use this, vmm_regex_build is assumed to have been
 *  called before this to compile the regex
 * Return 1 if there is a vmm_match
 */
int vmm_regex_compare(const char *str_to_match)
{
   int error_id;
   error_id = regexec(&preg,
              str_to_match,
              (size_t) REGEX_MAXMATCHES,
              pmatch,
              0);
   if (error_id != 0) {
     if (error_id == REG_NOMATCH) {
       return 0;
     }
     regerror(error_id,
              &preg,
              regex_errbuf,
              REGEX_ERRBUFSIZE); 
     printf("Can not compare string %0s: %s\n",str_to_match,regex_errbuf);
     return 0;
   }
   if (pmatch[0].rm_so >= 0) return(1);
   return 0;
}

/*
 * Return 1 if there is a vmm_match
 */
int vmm_regex(const char *str_to_match,
                  const char *regex_str) 
{
  int retval;
  
  if (str_to_match_global != NULL) free(str_to_match_global);
  if (regex_str_global != NULL) free(regex_str_global);
  
  str_to_match_global = (char *) strdup(str_to_match);
  regex_str_global = (char *) strdup(regex_str);
  
  if (vmm_regex_build(regex_str_global) == 0) {
    if (vmm_regex_compare(str_to_match_global)) {
      return 1;
    }
  }

  return 0;
}

/*
 * vmm_str_backref(n)
 *   Returns the n-th backref.
 *   Assumes string has been stored in global variable str_to_match_global
 *   Also assumes a prior vmm_match has been done, else returns a null string
 *   If backref does not exist, also returns null string
 * Storage is allocated by the callee and has to be managed by caller.
 */
char* vmm_str_backref(int n) 
{
   char *return_str;
   if (n >= REGEX_MAXMATCHES) {
      //return_str = strdup("");
      return_str = NULL;
   } else {
      if (last_matched)
         return_str = vmm_match_in_string(pmatch[n], 
                                   str_to_match_global,
                                   REGEX);
      else
         return_str = NULL;
   }
   return(return_str);
}


int vmm_str_match(const char *str_to_match,
                  const char *regex_str) {
   if (vmm_regex(str_to_match, regex_str)) {
      vmm_match_in_string(pmatch[0], 
                          str_to_match_global,
                          REGEX);
      last_matched = 1;
   } else {
      /* clean out the buffers */
      last_matched = 0;
   }

   return(last_matched);
}


char* vmm_str_prematch() {
   char *return_str;
   if (last_matched) 
      return_str = vmm_match_in_string(pmatch[0], 
                                str_to_match_global,
                                REGEX_PRE);
   else
      return_str = NULL;
   return(return_str);
}

char* vmm_str_postmatch() {
   char *return_str;
   if (last_matched)
      return_str = vmm_match_in_string(pmatch[0], 
                                str_to_match_global,
                                REGEX_POST);
   else
      return_str = NULL;
   return(return_str);
}

#endif


#ifdef TEST

void debug_print(const char* str_to_match,
            const char* regex_str) {
   char* strtmp;
   int i;
   printf("Str: %s\n", str_to_match);
   printf("Regex %s\n", regex_str);
   if(vmm_str_match(str_to_match_global, regex_str_global)) {
      printf("Pre: %s\n",vmm_str_prematch());
      printf("Post: %s\n",vmm_str_postmatch());
   }
   i = 0;
   while (strcmp((strtmp = vmm_str_backref(++i)),"") != 0) {
      printf("Backref[%0d]: %s\n",i,strtmp);
      free(strtmp);
   }

   return;
}

int main() 
{

   debug_print("invalid this valid routine- invalid",
         "(v.*id).*this.*routine.*(in.*d)");
   
   debug_print("invalid this valid routine- invalid",
               "rout.*-");
   
   debug_print("invalid this valid routine- invalid",
               "((va.*d).*-).*(li)d");
   

   return(1);

}
#endif

