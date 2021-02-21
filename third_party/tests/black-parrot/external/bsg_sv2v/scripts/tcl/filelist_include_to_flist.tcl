
set DESIGN_DIR $::env(DESIGN_DIR)
set PROCESS    $::env(PROCESS)

source ${DESIGN_DIR}/tcl/filelist.tcl
source ${DESIGN_DIR}/tcl/include.tcl

if { [file exists ${DESIGN_DIR}/tcl/hard/${PROCESS}/filelist_deltas.tcl] } {
  source ${DESIGN_DIR}/tcl/hard/${PROCESS}/filelist_deltas.tcl
} else {
  set HARD_SWAP_FILELIST [join ""]
  set NETLIST_SOURCE_FILES [join ""]
  set NEW_SVERILOG_SOURCE_FILES [join ""]
}

set hard_swap_module_list [list]
foreach f $HARD_SWAP_FILELIST {
  lappend hard_swap_module_list [file rootname [file tail $f]]
}

set sverilog_source_files [list]
foreach f $SVERILOG_SOURCE_FILES {
  set module_name [file rootname [file tail $f]]
  set idx [lsearch $hard_swap_module_list $module_name]
  if {$idx == -1} {
    lappend sverilog_source_files $f
  } else {
    lappend sverilog_source_files [lindex $HARD_SWAP_FILELIST $idx]
  }
}

set final_netlist_source_files $NETLIST_SOURCE_FILES
set final_sverilog_source_files [concat $sverilog_source_files $NEW_SVERILOG_SOURCE_FILES]
set all_final_source_files [concat $final_netlist_source_files $final_sverilog_source_files]

set final_sverilog_include_paths [list]
foreach incdir $SVERILOG_INCLUDE_PATHS {
  # replace 'portable' directories with the target process
  # TODO: for now, no replacements are done to the packaging directory
  #lappend final_sverilog_include_paths [regsub -all portable $incdir $::env(BSG_PACKAGING_FOUNDRY)]
  lappend final_sverilog_include_paths $incdir
}

set final_sverilog_include_paths [join "$final_sverilog_include_paths"]

foreach i $final_sverilog_include_paths {
  puts "+incdir+$i"
}

foreach i $all_final_source_files {
  puts "$i"
}

