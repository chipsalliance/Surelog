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


#include "tcl.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <malloc.h>
#include "vcsuser.h"
#ifndef TESTING
#include "svdpi.h"
#endif

/* user defined types */

/* basic type which will be passed to Verilog,
 *  maps to the xvc_parse_cmd class in xvc_manager
 */
typedef struct xvc_parse_cmd {
   int  argc;
   char **argv;    /* arg list */ 
   char *testfile; /* source file */
   char *linec;    /* line no.*/
   char *err_msg;  /* error msg seen in parsing */
   struct xvc_parse_cmd *next;
} xvc_parse_cmd_t;

/*List of xvc_cmds and associated functions to maintain list*/
/* Note: need this right now, as DPI export functions to dynamic
 * types are not yet supported. Hence, need to keep the complete
 * set of commands in a list, and at the end of processing
 * iterate over the list elements one-by-one
 */
xvc_parse_cmd_t *xvc_cmd_list;
xvc_parse_cmd_t *xvc_current_cmd_read_p; /* read pointer */
xvc_parse_cmd_t *xvc_current_cmd_p;
char *xvc_current_err_msg;

/* Globals */

Tcl_Interp *xvc_tcl_interp;

/* Prototypes and functions */
int xvc_put_cmd_args(
                 ClientData clientData, 
                 Tcl_Interp *interp, 
                 int argc, 
                 char *argv[]) ;

int xvc_error_handler(
                 ClientData clientData, 
                 Tcl_Interp *interp, 
                 int argc, 
                 char *argv[]) ;

void xvc_register_tcl_functions () ;

int xvc_tcl_init () ;

xvc_parse_cmd_t *xvc_cmd_copy(xvc_parse_cmd_t xvc_cmd) ;

void xvc_cmd_free(xvc_parse_cmd_t *xvc_cmd) ;

void xvc_cmd_free_all() ;

void xvc_add_item(xvc_parse_cmd_t *xvc_cmd) ;

void xvc_cmd_print(xvc_parse_cmd_t *cmd) ;

xvc_parse_cmd_t *xvc_get_cmd() ;

int vmm_xvc_get_next_cmd(int *argc_p,
                     char **argv,
                     char **testfile_p,
                     char **linec_p,
                     char **err_msg_p) ;

/* Functions to manipulate xvc_cmd_list */
xvc_parse_cmd_t *xvc_cmd_copy(xvc_parse_cmd_t xvc_cmd) {
   int i;
   xvc_parse_cmd_t *item;
   item = (xvc_parse_cmd_t *) malloc (sizeof(xvc_parse_cmd_t));
   item->argc = xvc_cmd.argc; 
   item->testfile = strdup(xvc_cmd.testfile);
   item->linec    = strdup(xvc_cmd.linec);
   item->argv     = (char **) malloc(sizeof(char **)*(item->argc));
   for (i = 0; i < item->argc; i++) {
      /* ignore the first ie., "put_cmd_args" */
      item->argv[i] = strdup(xvc_cmd.argv[i]);
   }
   item->next = xvc_cmd.next;
   return (item);
}

/* frees up the internals of xvc_cmd, and xvc_cmd itself */
void xvc_cmd_free(xvc_parse_cmd_t *xvc_cmd) {
   int i;
   if (xvc_cmd == NULL) 
      return;
   free(xvc_cmd->testfile);
   free(xvc_cmd->linec);
   for (i = 0; i < xvc_cmd->argc; i++) {
      free(xvc_cmd->argv[i]);
   }
   free(xvc_cmd->argv);
   if (xvc_cmd->err_msg)
      free(xvc_cmd->err_msg);
   free(xvc_cmd);
}

/* adds to end of the global linked list */
void xvc_add_item(xvc_parse_cmd_t *xvc_cmd) {
   xvc_parse_cmd_t *tmp;
   xvc_cmd->next = NULL;
   if (xvc_cmd_list == NULL) {
      xvc_cmd_list = xvc_cmd;
      xvc_current_cmd_read_p = xvc_cmd_list; /* init the read pointer */
   } else {
      /* walk along list to the end */
      for (tmp = xvc_cmd_list; 
           tmp->next != NULL; 
           tmp = tmp->next);
      tmp->next = xvc_cmd;
   }
}

/* print */
void xvc_cmd_print(xvc_parse_cmd_t *cmd) {
  int i;
  io_printf("-------DPI: %s[%s] -------\n",
         cmd->testfile,
         cmd->linec);
  for (i = 0; i < cmd->argc; i++) {
     io_printf("   %s\n", cmd->argv[i]); 
  }
  if (cmd->err_msg)
     io_printf("   %s\n", cmd->err_msg);
}

/* gets from the current read ptr of the list */
/* note, it is the caller's responsibility to free up the
 * returned cmd after work on it is done
 */
xvc_parse_cmd_t *xvc_get_cmd() {
   xvc_parse_cmd_t *retval;
   if (xvc_cmd_list) {
      retval = xvc_current_cmd_read_p;
      if (xvc_current_cmd_read_p)
         xvc_current_cmd_read_p = xvc_current_cmd_read_p->next;
   } else {
      retval = NULL;
   }

   return(retval);
}

/* delete the entire list */
void xvc_cmd_free_all() {
   xvc_parse_cmd_t *item;
   while (xvc_cmd_list != NULL) {
      item = xvc_cmd_list->next;
      xvc_cmd_free(xvc_cmd_list);
      xvc_cmd_list = item;
   }
   xvc_current_cmd_read_p = NULL; /* reset read pointer also */
}

/* on being called, send the current head of the list to the
 * Verilog side. The list head also gets moved
 * Since the verilog side makes a copy, this function also
 * frees up memory of the current command when done
 * Returns 1 if valid entry, 0 if empty, or some other error
 */
int vmm_xvc_get_next_cmd(int *argc_p,
                     char **argv,
                     char **testfile_p,
                     char **linec_p,
                     char **err_msg_p) {

   int i;
   xvc_parse_cmd_t *item;

   if ((item = xvc_get_cmd()) == NULL)
      return (0);

   *argc_p = item->argc;
   *testfile_p = item->testfile;
   *linec_p = item->linec;
   *err_msg_p = item->err_msg;
   for (i = 0; i < item->argc; i++) {
      argv[i] = item->argv[i];
   }

   return(1);
}

/* initialize TCL interpreter
 * Standard initialization and other init tasks, such
 *  as registering any TCL commands.
 * Return TCL_OK on success, TCL_ERROR on failure
 */
int xvc_tcl_init () {
  if ((xvc_tcl_interp = Tcl_CreateInterp()) == NULL)
    return (TCL_ERROR);

  return (TCL_OK);
}

void xvc_register_tcl_functions () {
  /* register user TCL functions */
  Tcl_CreateCommand(xvc_tcl_interp, 
                    "put_cmd_args", 
                    (void *) xvc_put_cmd_args, 
                    (ClientData) NULL, 
                    (Tcl_CmdDeleteProc *) NULL);

  /* register user TCL functions */
  Tcl_CreateCommand(xvc_tcl_interp, 
                    "xvc_error_handler", 
                    (void *) xvc_error_handler, 
                    (ClientData) NULL, 
                    (Tcl_CmdDeleteProc *) NULL);
  
}

/* error handling...
 * Argument is the error_msg
 * Append the err_msg to the error string of the current cmd
 ***/
int xvc_error_handler(
                 ClientData clientData, 
                 Tcl_Interp *interp, 
                 int argc, 
                 char *argv[]) {

   if (argc != 2)
      io_printf("xvc_manager: Unknown error !!\n");

#ifdef DEBUG_DPI
   io_printf("Error_C: %s\n",argv[1]);
#endif
  
   /* append to xvc_current_err_msg */
   if (xvc_current_err_msg == NULL)
      xvc_current_err_msg = strdup(argv[1]);

   return (TCL_OK);

}

/* C functions registered with TCL
 * Gets the arglist, file, linec and error msg in a command
 * The last two args are
 *    - file
 *    - linec
 * The args before this are the cmd line args.
 */

int xvc_put_cmd_args(
                 ClientData clientData, 
                 Tcl_Interp *interp, 
                 int argc, 
                 char *argv[]) {
   
  int i;

  xvc_current_cmd_p = (xvc_parse_cmd_t *) malloc (sizeof(xvc_parse_cmd_t));

  /* assign new data */
  xvc_current_cmd_p->argc = argc - 3; 
  xvc_current_cmd_p->testfile = strdup(argv[argc-2]);
  xvc_current_cmd_p->linec    = strdup(argv[argc-1]);
  xvc_current_cmd_p->argv     = (char **) 
                             malloc(sizeof(char **)*(xvc_current_cmd_p->argc));
  for (i = 0; i < xvc_current_cmd_p->argc; i++) {
     /* ignore the first ie., "put_cmd_args" */
     xvc_current_cmd_p->argv[i] = strdup(argv[i+1]);
  }
  /* put the current error msg into this cmd */
  xvc_current_cmd_p->err_msg = xvc_current_err_msg;


  /* put onto the linked list tail of commands */
  xvc_add_item(xvc_current_cmd_p);

  #ifdef DEBUG_DPI
  xvc_cmd_print(xvc_current_cmd_p);
  #endif

  return TCL_OK;
}

void
vmm_xvc_tcl_execute_file(char *test_file) {
   int tcl_error;

   char xvc_home_path[200];  
   char *xvc_tcl_utils_file_fullpath;
   char xvc_tcl_cmd_buf[1000];

   /* perform creation and inits of the TCL interpreter */
   tcl_error = xvc_tcl_init();
   if (tcl_error != TCL_OK) {
      io_printf("Error in initialization of TCL for VMM xvc manager\n");
      abort();
   }

   /* Source the startup script */
   /* Check for +vmm_path=%s string, if present, it overrides
      VCS_HOME/etc/vmm as the location to pickup the vmm_xvc_parse.tcl
      initialization file */
   if (mc_scan_plusargs("vmm_path")) {
      char *str;
      str = mc_scan_plusargs("vmm_path") + 1;
      strcpy(xvc_home_path,str);
      strcat(xvc_home_path,"/");
   } else {
      /* get VCS_HOME env. variable */
      char *vcs_home_path;
      vcs_home_path = getenv("VCS_HOME");
      if (vcs_home_path == NULL) {
         io_printf("VCS_HOME env. variable not set, needed for xvc manager\n");
         abort(); 
      }
      strcpy(xvc_home_path,vcs_home_path);
      strcat(xvc_home_path,"/etc/vmm/");
   }
   /* ToDo: Error out if xvc_home_path is NULL */
   xvc_tcl_utils_file_fullpath = strcat(xvc_home_path, "vmm_xvc_parse.tcl");

   tcl_error = Tcl_EvalFile(xvc_tcl_interp, xvc_tcl_utils_file_fullpath);
   if (tcl_error != TCL_OK) {
      io_printf("Error: xvc manager: could not eval file %s\n",xvc_tcl_utils_file_fullpath);
      io_printf("  Either +vmm_path=<str> or VCS_HOME env. variable needs to be provided\n");
      abort();
   }

   /* register user TCL functions */
   xvc_register_tcl_functions();

   /* execute the parse-start command from C */
   sprintf(xvc_tcl_cmd_buf, "execute_file %s", test_file);
   tcl_error = Tcl_Eval(xvc_tcl_interp, xvc_tcl_cmd_buf);
   if (tcl_error != TCL_OK) {
      io_printf("Error: xvc manager: in executing file %s: File does not exist ?\n",
         test_file);
      abort();
   }

}

#ifdef TESTING
int main() {

  vmm_xvc_tcl_execute_file("./TESTFILES/test.txt");

  /* print out the list of commands */
  /* iterate over the cmd list, and print them out one by one */
  {
     xvc_parse_cmd_t *item;
     while ((item = xvc_get_cmd())) {
        xvc_cmd_print(item);
     }
     xvc_cmd_free_all();

  }


}

#endif
