//----------------------------------------------------------------------
//   Copyright 2007-2011 Mentor Graphics Corporation
//   Copyright 2011 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------


#include <malloc.h>
#include <string.h>
#include <sys/types.h>
#include <regex.h>
#include "vpi_user.h"
//#include <stdio.h>


const char uvm_re_bracket_char = '/';
static char uvm_re[2048];


//--------------------------------------------------------------------
// uvm_re_match
//
// Match a string to a regular expression.  The regex is first lookup
// up in the regex cache to see if it has already been compiled.  If
// so, the compile version is retrieved from the cache.  Otherwise, it
// is compiled and cached for future use.  After compilation the
// matching is done using regexec().
//--------------------------------------------------------------------
int uvm_re_match(const char * re, const char *str)
{
  regex_t *rexp;
  int err;
  int len = strlen(re);
  char * rex = &uvm_re[0];

  // safety check.  Args should never be null since this is called
  // from DPI.  But we'll check anyway.
  if(re == NULL)
    return 1;
  if(str == NULL)
    return 1;

  /*
  if (len == 0) {
    vpi_printf((PLI_BYTE8*)  "UVM_ERROR: uvm_re_match : regular expression empty\n");
    return 1;
  }
  */
  if (len > 2040) {
    vpi_printf((PLI_BYTE8*)  "UVM_ERROR: uvm_re_match : regular expression greater than max 2040: |%s|\n",re);
    return 1;
  }

  // we copy the regexp because we need to remove any brackets around it
  strcpy(&uvm_re[0],re);
  if (len>1 && (re[0] == uvm_re_bracket_char) && re[len-1] == uvm_re_bracket_char) {
    uvm_re[len-1] = '\0';
    rex++;
  }

  rexp = (regex_t*)malloc(sizeof(regex_t));

  if (rexp == NULL) {
    vpi_printf((PLI_BYTE8*)  "UVM_ERROR: uvm_re_match: internal memory allocation error");
    return 1;
  }

  err = regcomp(rexp, rex, REG_EXTENDED);

  if (err != 0) {
    vpi_printf((PLI_BYTE8*)  "UVM_ERROR: uvm_re_match: invalid glob or regular expression: |%s|\n",re);
    regfree(rexp);
    free(rexp);
    return err;
  }

  err = regexec(rexp, str, 0, NULL, 0);

  //vpi_printf((PLI_BYTE8*)  "UVM_INFO: uvm_re_match: re=%s str=%s ERR=%0d\n",rex,str,err);

  regfree(rexp);
  free(rexp);

  return err;
}


//--------------------------------------------------------------------
// uvm_glob_to_re
//
// Convert a glob expression to a normal regular expression.
//--------------------------------------------------------------------

const char * uvm_glob_to_re(const char *glob)
{
  const char *p;
  int len;

  // safety check.  Glob should never be null since this is called
  // from DPI.  But we'll check anyway.
  if(glob == NULL)
    return NULL;

  len = strlen(glob);

  if (len > 2040) {
    vpi_printf((PLI_BYTE8*)  "UVM_ERROR: uvm_glob_to_re : glob expression greater than max 2040: |%s|\n",glob);
    return glob;
  }

  // If either of the following cases appear then return an empty string
  //
  //  1.  The glob string is empty (it has zero characters)
  //  2.  The glob string has a single character that is the
  //      uvm_re_bracket_char  (i.e. "/")
  if(len == 0 || (len == 1 && *glob == uvm_re_bracket_char))
  {
    uvm_re[0] = '\0';
    return &uvm_re[0];  // return an empty string
  }

  // If bracketed with the /glob/, then it's already a regex
  if(glob[0] == uvm_re_bracket_char && glob[len-1] == uvm_re_bracket_char)
  {
    strcpy(uvm_re,glob);
    return &uvm_re[0];
  }
  else
  {
    // Convert the glob to a true regular expression (Posix syntax)
    len = 0;

    uvm_re[len++] = uvm_re_bracket_char;

    // ^ goes at the beginning...
    if (*glob != '^')
      uvm_re[len++] = '^';

    for(p = glob; *p; p++)
    {
      // Replace the glob metacharacters with corresponding regular
      // expression metacharacters.
      switch(*p)
      {
      case '*':
        uvm_re[len++] = '.';
        uvm_re[len++] = '*';
        break;

      case '+':
        uvm_re[len++] = '.';
        uvm_re[len++] = '+';
        break;
        
      case '.':
        uvm_re[len++] = '\\';
        uvm_re[len++] = '.';
        break;
        
      case '?':
        uvm_re[len++] = '.';
        break;

      case '[':
        uvm_re[len++] = '\\';
        uvm_re[len++] = '[';
        break;

      case ']':
        uvm_re[len++] = '\\';
        uvm_re[len++] = ']';
        break;

      case '(':
        uvm_re[len++] = '\\';
        uvm_re[len++] = '(';
        break;

      case ')':
        uvm_re[len++] = '\\';
        uvm_re[len++] = ')';
        break;
        
      default:
        uvm_re[len++] = *p;
        break;
      }
    }
  }

  // Let's check to see if the regular expression is bounded by ^ at
  // the beginning and $ at the end.  If not, add those characters in
  // the appropriate position.

  if (uvm_re[len-1] != '$')
    uvm_re[len++] = '$';

  uvm_re[len++] = uvm_re_bracket_char;

  uvm_re[len++] = '\0';

  return &uvm_re[0];
}


//--------------------------------------------------------------------
// uvm_dump_re_cache
//
// Dumps the set of regular expressions stored in the cache
//--------------------------------------------------------------------

void uvm_dump_re_cache()
{
  vpi_printf((PLI_BYTE8*)  "uvm_dump_re_cache: cache not implemented");
}

