#;/ 
#;/ -------------------------------------------------------------
#;/    Copyright 2004-2008 Synopsys, Inc.
#;/    All Rights Reserved Worldwide
#;/ 
#;/    Licensed under the Apache License, Version 2.0 (the
#;/    "License"); you may not use this file except in
#;/    compliance with the License.  You may obtain a copy of
#;/    the License at
#;/ 
#;/        http:;/www.apache.org/licenses/LICENSE-2.0
#;/ 
#;/    Unless required by applicable law or agreed to in
#;/    writing, software distributed under the License is
#;/    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
#;/    CONDITIONS OF ANY KIND, either express or implied.  See
#;/    the License for the specific language governing
#;/    permissions and limitations under the License.
#;/ -------------------------------------------------------------
#;/ 


;# VMM syntax parser in TCL

    set vmm_tcl_mode 0 ;# 1: pure tcl, 0: xvc syntax

    set current_filename ""
    set current_lineno 0
    set current_cmd ""
    set current_errmsg " "

    set errInfo ""

    set xvc_parse_debug 0

    ;# flags used for checks
    set flag(execute_seen) 0  ;# if execute command is seen
    set flag(misc_seen)    0  ;# if ^verbosity,stoponerror,stoponevent

    ;#################################################
    proc send_to_c {args} {
       if {$::xvc_parse_debug} {
          puts "TCL: [join $args] $::current_filename $::current_lineno"

       }
       eval put_cmd_args [join $args] \
           $::current_filename $::current_lineno
    }

     
    ;# default, overridden in C code
    proc put_cmd_args {args} {
       puts "---------------------------------------"    
       foreach elem $args {
       puts "$elem"
       }
    }

    ;##################################################
    ;# stack and its operations
    ;##################################################

    set file_stack {}    ;# list of open files

    ;#returns filename
    ;#note: each item is a list of {filename chan lineno}
    proc stack_item_fname {stack_item} {
      return [lindex $stack_item 0]
    }
    ;#returns lineno
    proc stack_item_lineno {stack_item} {
      return [lindex $stack_item 2]
    }
    ;#returns channel
    proc stack_item_chan {stack_item} {
      return [lindex $stack_item 1]
    }
    ;#creates a record of {filename, lineno, chan} to put onto stack
    proc stack_return_item {filename chan lineno} {
       set stack_item {}
       lappend stack_item $filename $chan $lineno 
       return $stack_item
    }
    ;# push at the end
    proc stack_push {stack_item} {
       lappend ::file_stack $stack_item
    }
    ;# pop from the end
    proc stack_pop {} {
       set stack_length [llength $::file_stack]
       set stack_lastindex [expr $stack_length - 1]
       if {$stack_length > 0} {
	  set return_item [lindex $::file_stack $stack_lastindex]
	  set ::file_stack [lreplace $::file_stack $stack_lastindex $stack_lastindex]
       } else {
	  puts "Empty-stack"
	  set return_item {}
       }
       return $return_item
    }
    ;# get from the top, without popping
    proc stack_peek {} {
       set stack_length [llength $::file_stack]
       set stack_lastindex [expr $stack_length - 1]
       if {$stack_length > 0} {
	  set return_item [lindex $::file_stack $stack_lastindex]
       } else {
	  ;# done when we are here
          ;# toDo: return control to the callee application
          ;# puts "Empty-stack"
	  set return_item {}
       }
       return $return_item
    }
    ;# update the line number of the top of the stack..(current file)
    ;# ToDo: redo this more efficiently.
    proc stack_top_update {lineno} {
       ;# basically, pop the stack, replace it and push it back.
       set top_item [stack_pop]
       ;# replace line no (index 2)
       set top_item [lreplace $top_item 2 2 $lineno]
       stack_push $top_item
    }

    ;#size of the stack
    proc stack_size {} {
       return [llength $::file_stack]
    }
    ;# is_empty
    proc stack_isempty {} {
       set stack_length [llength $::file_stack]
       if {$stack_length > 0} {
	  return 1
       } else {
	  return 0
       } 
    }


    ;######################################
    ;# error handler, put filename ,line number etc.
    proc error_handler {{msg "Unknown error"} {abort 0}} {

       set ::current_errmsg "Error: $::current_filename\[$::current_lineno\] $msg"
       xvc_error_handler $::current_errmsg
       if {$::xvc_parse_debug} {
          puts $msg
          ;# in case stack info is needed
          ;# puts $::errorInfo
       }
       if {$abort == 1} {
	  exit
       }
    }

    ;# default, overridden in C code.
    proc xvc_error_handler {msg} {
       puts $msg
    }

    ;#If variable exists, return the name as "$var", else
    ;#  return name of the variable itself 
    proc get_symtab {key}  {
       if { [regexp {[\s\t\$]} $key] == 1} {
          return $key
       }
       if { [uplevel #0 info exists $key] } {
         ;# return "\$$key"
          upvar #0 $key key1;
          return $key1
       } else {
          return $key
       }
    }

    ;# replace any words in the input list if they are keys
    ;#  in the symbol table by the value stored in symtab
    proc replace_from_symtab {list} {
       upvar $list listname
       set outlist {}
       foreach elem $listname {
          lappend outlist [get_symtab $elem]
       }
       return $outlist
    }


    ;# command table aliases(list of variants of known commands)
    variable cmdalias
    array set cmdalias { s        scenario }
    array set cmdalias { e        event }
    array set cmdalias { m        mapevent }
    array set cmdalias { a        action }
    array set cmdalias { i        interrupt }
    array set cmdalias { x        execute }
    ;#If key exists in cmd alias, return value, else
    ;#  return name of the key itself !
    proc get_cmdalias {key} {
       if { [info exists ::cmdalias($key)] } {
	  return $::cmdalias($key)
       } else {
	  return $key
       }
    }

    ;#args (argc, argv) array for returning back to C

    ;# check if command is complete
    proc info_complete { cmd } {

	if { [catch { info complete $cmd } value] } {
	    return 0
	}

	return $value
    }

    ;#XVC procedures
    proc execute_file {filename} {

       ;#open the file, line by line, keeping track of line numbers
       if { [catch { set chan [open $filename r] } msg] } {
	  error_handler $msg
	  return -code error "Error: $msg";
       }


       ;#start a new entry: push details onto on top of stack
       set lineno 0
       set ::current_lineno 0
       set ::current_filename $filename
       stack_push [stack_return_item $filename $chan $lineno]
       

       #main loop: reading file, executing commands.
       set cmdbuf ""
       set ::current_cmd $cmdbuf
       set cmd_complete 1
       while { 1 } {

	  catch { gets $chan line }   ;# get next line
	  incr lineno
	  set ::current_lineno $lineno

	  if { [eof $chan] } {
	     if { ! $cmd_complete } {
		 error_handler "Command incomplete at EOF." 
	     }
	     break
	  }

	  ;#pre_process the line 
	  set tcl_line [preproc_line $line]

	  append cmdbuf $tcl_line

	  ;#if line is incomplete (i.,e curly braces), get new lines.
	  if { ! [info_complete $cmdbuf] } {
             append cmdbuf "\n"
	     set cmd_complete 0
	     continue
	  }
          ;#if line ends in backslash get new line
          if { [regexp {\\[\s\t]*$} $tcl_line] == 1} {
             regsub {\\[\s\t]*$} $cmdbuf {} cmdbuf
	     set cmd_complete 0
	     continue
          }
          set ::current_cmd $cmdbuf

	  ;# execute the cmd
	  execute_cmd $cmdbuf

	  ;# push line no. onto top of stack
	  stack_top_update $lineno

	  ;# reset cmdbuf to receive new command
	  set cmdbuf ""
          set ::current_cmd $cmdbuf
	  set cmd_complete 1

       }

       ;# pop when done with the file
       set throw_away [stack_pop]

       ;# need to set the line number and the filename from the top of
       ;#  stack now.  
       set stack_item [stack_peek]
       set chan [stack_item_chan $stack_item]
       set filename [stack_item_fname $stack_item] 
       set lineno [stack_item_lineno $stack_item]
       set ::current_lineno 0
       set ::current_filename $filename
    }

    ;# execute the command
    proc execute_cmd {str} {
       ;# dont do anything for null command
       if { [regexp {^[\s\\\n]*$} $str] } {
          return;
       }

       #; 7. make all the first words lower case, and replace them by their
       #; aliases
       #; i.,e X -> execute, i -> interrupt, ACTION -> action etc.,

       ;# remove leading whitespace if any
       regsub {^[\s\t]+} $str {} str

       set tmplist [split $str]
       set tmpfirstword [get_cmdalias [string tolower [lindex $tmplist 0]]]
       set str [join [lreplace $tmplist 0 0 $tmpfirstword]]


       ;# execute the cmd
       ;# the 'uplevel #0' flattens the str, hence its enclosed in a list
       if { [catch {uplevel #0 eval [list $str]} msg ] } {
          error_handler $msg
       } 

    }

    ;# preprocess the line, convert to TCL format
    ;# Make the following modifications in VMM mode (vmm_tcl_mode 0):
    ;#   1. Change #define -> set
    ;#   2. Change #include -> include
    ;#   3. Remove comments i.,e "//.*" 
    ;#   4. Replace '$$' with '\$'
    ;#   5. Replace '$foo' with '$env(foo)'
    ;#   6. Handle env. Variable substitutions
    ;#   7. Replace commands with their aliases
    ;# Make the following modifications to either mode
    ;#   1. escaped quotes: protect escape char 
    ;#   2. in a quoted string, escape chars should be
    ;#      protected - ToDo

    proc preproc_line {str} {

      ;# make changes to string which apply to both
      ;#   pure TCL and VMM syntax
      ;#   1. escaped quotes: protect escape char 
      ;#   2. in a quoted string, escape chars should be
      ;#      protected - ToDo
      regsub {\\"} $str {\\\"} str

      ;# if its in PURE TCL mode, return now
      if { $::vmm_tcl_mode == 1 } {
	     return $str
      }

      ;# 3. remove all comments i.,e '//.*'
      regsub {//.*} $str {} str

      ;# 4. if you see a $$, replace it with \$ , add extra '\' as
      ;#    they get stripped off by later subst
      regsub -all {\$\$} $str {\\\\\$} str

      ;# 5. if you see a $foo (but not a \$foo), replace with the
      ;#    environment variable ::env($foo): -> Ugly regexp hack !
      ;# ToDo: this doesnt seem to work for variables like $foo$foo
      regsub -all {([^\\])\$([^\t\s\$\\\/]*)} $str {\1$::env(\2)} str
      ;# special case: replace the first char '$'
      regsub {^\$([^\t\s\$\\\/]*)} $str {$::env(\1)} str

      ;# 6. replace all env variables in the string..
      if { [catch {set str [subst $str]} msg] } {
         error_handler "Env. variable not set: $msg"
      }
       
      ;# 1. change #define to define
      regsub -nocase -all {\#define} $str {define} str

      ;# 2. change #include
      regsub -nocase -all {\#include} $str {include} str

      return $str
    }

    ;# check number of args, to be between arg1 and arg2 in length
    proc arg_num_check {list l1 {l2 1000}} {
        upvar $list listname
        set listlength [llength $listname]
        if { $listlength < $l1 } {
            error_handler "Too few arguments."
        }
        if { $listlength > $l2 } {
            error_handler "Too many arguments."
        }
    }

    ;# xvc_parse_debug print helpers
    proc dprint {msg} {
       if { $::xvc_parse_debug == 1} {
          puts "Debug:$::current_filename\[$::current_lineno\] $msg"
       }
    }
    proc dprint_args {list} {
       upvar $list listname
       if { $::xvc_parse_debug == 1} {
          foreach elem $listname {
             puts "\t$elem"
          }
       }
    }

    ;####################################################
    ;# commands which form part of the xvc manager spec
    ;####################################################

    proc define {args} {
       set args [replace_from_symtab args]
       arg_num_check args 2 2
       ;# set the value of the variable in global scope
       ;# upvar #0 [lindex args 1] key
       ;# set key [lindex args 2]
       uplevel #0 eval "set [join $args]"
    }
 
    proc include {args} {
       set args [replace_from_symtab args]
       arg_num_check args 1 1

       set include_fname [lindex $args 0]

       ;# interpret relative paths as relative to current file
       set include_fname [file join [file dir $::current_filename] $include_fname]

       ;# handle as a new file..
       execute_file $include_fname
    }

    ;# same as include, except filenames are not relative paths..
    proc source {args} {
       set args [replace_from_symtab args]
       dprint "Source [join $args]"
       dprint_args args
       arg_num_check args 1 1

       set include_fname [lindex $args 0]

       ;# handle as a new file..
       execute_file $include_fname
    }

    proc verbosity {args} {
       set args [replace_from_symtab args]

       ;# checks
       arg_num_check args 2 2
       if {$::flag(misc_seen)} {
          error_handler "Verbosity cannot appear after cmds except stoponerror, stoponevent" 
       }

       send_to_c verbosity $args 
    }

    ;# log command
    ;#  1. illegal for log to be in an included file.
    proc log {args} {
       set args [replace_from_symtab args]
       arg_num_check args 1 2
       if {$::flag(execute_seen)} {
          error_handler "An execute was seen prior to this command"
       }
       set ::flag(misc_seen) 1

       send_to_c log $args 
    }

    proc xvctrace {args} {
       set args [replace_from_symtab args]
       arg_num_check args 1 2
       if {$::flag(execute_seen)} {
          error_handler "An execute was seen prior to this command"
       }
       set ::flag(misc_seen) 1

       send_to_c xvctrace $args 
    }

    proc covfile {args} {
       set args [replace_from_symtab args]
       arg_num_check args 1 1
       if {$::flag(execute_seen)} {
          error_handler "An execute was seen prior to this command"
       }
       set ::flag(misc_seen) 1

       send_to_c covfile $args 
    }

    ;# stoponerror command
    ;#  1. illegal for stoponerror to be in an included file. - to confirm
    proc stoponerror {args} {
       set args [replace_from_symtab args]
       arg_num_check args 1 1
       if {$::flag(misc_seen)} {
          error_handler "Stoponerror cannot appear after cmds except verbosity, stoponevent" 
       }

       ;# illegal for stop_on_error to be in an included file
       ;# if { [llength $::file_stack] > 2 } {
       ;#    error_handler "stoponerror illegal in an included file."
       ;# }

       ;# illegal for arg0(count) < 1
       if {[lindex $args 0] < 1} {
          error_handler "stoponerror count should be >= 1."
       }

       send_to_c stoponerror $args 
    }

    proc stoponevent {args} {
       set args [replace_from_symtab args]
       arg_num_check args 2 3
       if {$::flag(misc_seen)} {
          error_handler "Stoponevent cannot appear after cmds except stoponerror, verbosity" 
       }

       ;# illegal for arg2(count) < 1
       if {[llength $args] == 3} {
          if {[lindex $args 2] < 1} {
             error_handler "stoponevent count should be >= 1."
          }
       }

       send_to_c stoponevent $args 
    }

    proc scenario {args} {
       set args [replace_from_symtab args]
       arg_num_check args 1 2
       if {$::flag(execute_seen)} {
          error_handler "An execute was seen prior to this command"
       }
       set ::flag(misc_seen) 1

       ;# illegal for arg0(count) < 1
       if {[lindex $args 0] < 0} {
          error_handler "Scenario id must be > 0"
       }

       send_to_c scenario $args 

    }

    ;# E[VENT] [ONESHOT] [LOCAL|GLOBAL] \
    ;#    (<sev>|<gev>) IS [<sid>.]<sev>{(,|+)[<sid>.]<sev>} [<descr>]  
    proc event {args} {
       set args [replace_from_symtab args]
       arg_num_check args 4 
       if {$::flag(execute_seen)} {
          error_handler "An execute was seen prior to this command"
       }
       set ::flag(misc_seen) 1

       ;# the compound event following IS should be stripped of whitespace

       ;# get index of is function
       set tmp1 [lsearch -regexp $args "(is|IS|iS|Is)"]
       ;# get the args after list into a string
       set str [join [lrange $args [expr $tmp1 + 1] [expr [llength $args] -1]]]
       ;# get hold of the cpd string and optional description
       regsub -all {(^[0-9\.\+\,\s\t]+)(.*)} $str {\1} cpdstr
       regsub -all {(^[0-9\.\+\,\s\t]+)(.*)} $str {\2} descr
       ;# remove all spaces out of the cpd description
       regsub -all {[\s\t]*} $cpdstr {} cpdstr

       ;# assemble it all back i.,e the original string,
       ;#    cpdstr and the description
       set args [lrange $args 0 $tmp1] 
       lappend args $cpdstr
       if {$descr != ""} {
          lappend args $descr
       }

       send_to_c event $args 
    }

    proc mapevent {args} {
       set args [replace_from_symtab args]
       arg_num_check args 5 
       if {$::flag(execute_seen)} {
          error_handler "An execute was seen prior to this command"
       }
       set ::flag(misc_seen) 1

       send_to_c mapevent $args 
    }

    proc action {args} {
       set args [replace_from_symtab args]
       arg_num_check args 2 
       if {$::flag(execute_seen)} {
          error_handler "An execute was seen prior to this command"
       }
       set ::flag(misc_seen) 1

       send_to_c action $args 
    }

    proc interrupt {args} {
       set args [replace_from_symtab args]
       arg_num_check args 2 
       if {$::flag(execute_seen)} {
          error_handler "An execute was seen prior to this command"
       }
       set ::flag(misc_seen) 1

       send_to_c interrupt $args 
    }

    proc execute {args} {
       set args [replace_from_symtab args]
       arg_num_check args 1 
       set ::flag(execute_seen) 1
       set ::flag(misc_seen) 1

       send_to_c execute $args 
    }


