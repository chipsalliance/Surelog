//
//------------------------------------------------------------------------------
//   Copyright 2011 Mentor Graphics Corporation
//   Copyright 2011 Cadence Design Systems, Inc. 
//   Copyright 2011 Synopsys, Inc.
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
//------------------------------------------------------------------------------

#include <string.h>
#include <stdio.h>
#include <malloc.h>
#include <regex.h>
#include <assert.h>
#include "vpi_user.h"

#define ARGV_STACK_PTR_SIZE 32

extern const char *uvm_dpi_get_next_arg_c ()
{
  s_vpi_vlog_info info;
  static char*** argv_stack = NULL;
  static int argv_stack_ptr = 0; // stack ptr

  if(argv_stack == NULL)
  {
    argv_stack = (char***) malloc (sizeof(char**)*ARGV_STACK_PTR_SIZE);
    vpi_get_vlog_info(&info);
    argv_stack[0] = info.argv;
  }

  // until we have returned a value
  while (1)
  {
    // at end of current array?, pop stack
    if (*argv_stack[argv_stack_ptr]  == NULL)
    {
      // stack empty?
      if (argv_stack_ptr == 0)
      {
	// reset stack for next time
	argv_stack = NULL;
        argv_stack_ptr = 0;
	// return completion
        return NULL;
      }
      // pop stack
      --argv_stack_ptr;
      // return indicator that we are popping stack
      return "__-f__";
    }
    else
    {
      // check for -f indicating pointer to new array
      if(0==strcmp(*argv_stack[argv_stack_ptr], "-f") ||
         0==strcmp(*argv_stack[argv_stack_ptr], "-F") )
      {
	char *r = *argv_stack[argv_stack_ptr];
	// bump past -f at current level
	++argv_stack[argv_stack_ptr]; 
	// push -f array argument onto stack
	argv_stack[argv_stack_ptr+1] = (char **)*argv_stack[argv_stack_ptr];
	// bump past -f argument at current level
	++argv_stack[argv_stack_ptr]; 
	// update stack pointer
	++argv_stack_ptr;
	assert(argv_stack_ptr < ARGV_STACK_PTR_SIZE);
	return r;
      }
      else
      {      
	// return current and move to next
	char *r = *argv_stack[argv_stack_ptr];
	++argv_stack[argv_stack_ptr];
	return r;
      }
    }
  }

}

extern char* uvm_dpi_get_tool_name_c ()
{
  s_vpi_vlog_info info;
  vpi_get_vlog_info(&info);
  return info.product;
}

extern char* uvm_dpi_get_tool_version_c ()
{
  s_vpi_vlog_info info;
  vpi_get_vlog_info(&info);
  return info.version;
}

extern regex_t* uvm_dpi_regcomp (char* pattern)
{
  regex_t* re = (regex_t*) malloc (sizeof(regex_t));
  int status = regcomp(re, pattern, REG_NOSUB|REG_EXTENDED);
  if(status)
  {
    vpi_printf((char *)"Unable to compile regex: %s\n", pattern);
    vpi_printf((char *)"Element 0 is: %c\n", pattern[0]);
    return NULL;
  }
  return re;
}

extern int uvm_dpi_regexec (regex_t* re, char* str)
{
  if(!re )
  {
    return 1;
  }
  return regexec(re, str, (size_t)0, NULL, 0);
}

extern void uvm_dpi_regfree (regex_t* re)
{
  if(!re) return;
  regfree(re);
  free (re);
}
