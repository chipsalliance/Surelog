# run_dc.tcl
#
# This is the main DesignCompiler script for the bsg_sv2v flow. The goal of
# this script is to read in the design and elaborate the top-level and output
# the elaborated netlist. Because we do not compile, there is no need for any
# technology files to be linked.

### Grab required ENV variables for the flow

set DESIGN_NAME      $::env(DESIGN_NAME)       ;# Top-level module
set DESIGN_FILELIST  $::env(DESIGN_FILELIST)   ;# Filelist path
set DESIGN_ELAB_NAME $::env(DESIGN_ELAB_NAME)  ;# Design name to elaborate
set OUTPUT_DIR       $::env(OUTPUT_DIR)        ;# Output directory
set OUTPUT_FILE      $::env(OUTPUT_ELAB_FILE)  ;# Output filename

### Application setup

set_svf -off                                                           ;# No need to svf file (for fomality)
set_app_var link_library                     ""                        ;# Empty link library
set_app_var target_library                   "*"                       ;# Default target library
set_app_var hdlin_infer_mux                  none                      ;# Use SELCT_OP over MUX_OP synthetic module
set_app_var sh_command_log_file              $OUTPUT_DIR/command.log   ;# Redirect command.log file
set_app_var verilogout_no_tri                true                      ;# Make unknown port connections wires not tris
set_app_var hdlin_ff_always_sync_set_reset   true                      ;# Try to infer synchronous set/reset logic
set_app_var hdlin_ff_always_async_set_reset  false                     ;# Don't try to infer asynchronous set/reset logic

### Read in the filelist

# Here we read in the filelist. For our designs, we often use VCS filelists to
# link the whole design together. Inside these filelists are 5 main items:
#
#   1. Comments        -- begging in the # character
#   2. +incdir+<path>  -- adding a search directory for includes
#   3. +define+<macro> -- adding a macro definition at compile time
#   4. -pvalue+<param> -- top-level parametes
#   5. <file>          -- verilog files
#
set bsg_incdirs  [list]
set bsg_macros   [list]
set bsg_params   [list]
set bsg_filelist [list]

set fid [open $DESIGN_FILELIST r]
while { [gets $fid line] >= 0 } {
  if { [regexp {^#.*} $line] } {
    continue
  } elseif { [regexp {^\+incdir\+(.*)} $line match sub] } {
    set incdir [regsub -all {\$(\w+)} $sub "\$::env\(\\1)"]
    puts "INFO: Adding $incdir to search path!"
    eval "lappend bsg_incdirs $incdir"
  } elseif { [regexp {^\+define\+(.*)} $line match sub] } {
    set macro [regsub -all {\$(\w+)} $sub "\$::env\(\\1)"]
    puts "INFO: Adding $macro to macros!"
    eval "lappend bsg_macros $macro"
  } elseif { [regexp {^\-pvalue\+(.*)} $line match sub] } {
    set param [regsub -all {\$(\w+)} $sub "\$::env\(\\1)"]
    puts "INFO: Adding $param to parameters!"
    eval "lappend bsg_params $param"
  } elseif { [regexp {^(.*)} $line match sub] } {
    set f [regsub -all {\$(\w+)} $sub "\$::env\(\\1)"]
    puts "INFO: Adding $f to filelist!"
    eval "lappend bsg_filelist $f"
  }
}

### Setup the search path with the include directories

set_app_var search_path "$search_path [join $bsg_incdirs]"

### Perform analysis

define_design_lib WORK -path $OUTPUT_DIR/${DESIGN_NAME}_WORK
if { ![analyze -format sverilog -define $bsg_macros [join $bsg_filelist]] } {
  exit 1
}

### Perform elaboration

if { $DESIGN_ELAB_NAME == "" } {
    set DESIGN_ELAB_NAME $DESIGN_NAME
}

if { ![elaborate -param [join $bsg_params ","] $DESIGN_ELAB_NAME] } {
  exit 1
}

### Rename and set the real top-level design

if { [sizeof_collection [get_designs -quiet $DESIGN_NAME]] == 0 } {
  set designs [get_designs -quiet -filter "@hdl_template == $DESIGN_NAME"]
  if { [sizeof_collection $designs] > 1 } {
    puts "Error: Toplevel design has multiple instances post-elaboration. This"
    puts "usually indicates that there are multiple parameterizations of the design."
    puts "This flow does not support different parameterizations of the top-level"
    puts "compile target, consider using a wrapper to uniqify the hierarchy for each"
    puts "parameter."
    exit 1
  } else {
    rename_design $designs $DESIGN_NAME
  }
}

### Make suer the current design is correct

current_design $DESIGN_NAME

### Cleanup some of the netlist

define_name_rules rules \
  -special verilog \
  -dummy_net_prefix "sv2v_dc_%d" \
  -flatten_multi_dimension_busses \
  -remove_irregular_net_bus \
  -remove_irregular_port_bus \
  -restricted {!@#$%^&*()\\-[]}
change_names -hier -rules rules

### Read in the constraints file if it exists

if {[file exists $::env(DESIGN_CONSTRAINTS_FILE)]} {
	if {[file extension $::env(DESIGN_CONSTRAINTS_FILE)] == ".sdc"} {
		read_sdc -echo $::env(DESIGN_CONSTRAINTS_FILE)
	} else {
		source -echo -verbose $::env(DESIGN_CONSTRAINTS_FILE)
	}
}

### Output the elaborated netlist

write_file -format verilog -hier -output $OUTPUT_FILE

### Output the sdc constraints

if {[file exists $::env(DESIGN_CONSTRAINTS_FILE)]} {
  write_sdc -nosplit $OUTPUT_FILE.sdc
}

### Finished!

exit 0

