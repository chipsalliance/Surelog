#!/usr/bin/tclsh

# Copyright 2019 Alain Dargelas
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

#######################################
#    Surelog frontend for Yosys
#######################################
# Usage: yosys.tcl <Yosys Script>
#######################################
# Prints/Execute a Surelog command that
# loads the design specified by a Yosys
# script
#######################################

set SURELOG_FILE_LIST {}
set SURELOG_TOP_LEVEL ""

variable myLocation [file normalize [info script]]

proc getResourceDirectory {} {
    variable myLocation
    return [file dirname $myLocation]
}

proc surelog:log { text } {
    global SURELOG_LOG_FILE
    puts $text
    flush stdout
    if ![info exist SURELOG_LOG_FILE] {
	set SURELOG_LOG_FILE [open regression.log "w"]
    }
    puts $SURELOG_LOG_FILE $text
    flush $SURELOG_LOG_FILE
}


set SURELOG_IGNORE_CMD(abc) 1
set SURELOG_IGNORE_CMD(add) 1
set SURELOG_IGNORE_CMD(aigmap) 1
set SURELOG_IGNORE_CMD(alumacc) 1
set SURELOG_IGNORE_CMD(anlogic_determine_init) 1
set SURELOG_IGNORE_CMD(anlogic_eqn) 1
set SURELOG_IGNORE_CMD(assertpmux) 1
set SURELOG_IGNORE_CMD(async2sync) 1
set SURELOG_IGNORE_CMD(attrmap) 1
set SURELOG_IGNORE_CMD(attrmvcpmove) 1
set SURELOG_IGNORE_CMD(blackbox) 1
set SURELOG_IGNORE_CMD(bugpoint) 1
set SURELOG_IGNORE_CMD(cda) 1
set SURELOG_IGNORE_CMD(check) 1
set SURELOG_IGNORE_CMD(chformal) 1
set SURELOG_IGNORE_CMD(chparam) 1
set SURELOG_IGNORE_CMD(chtype) 1
set SURELOG_IGNORE_CMD(clean) 1
set SURELOG_IGNORE_CMD(clk2fflogic) 1
set SURELOG_IGNORE_CMD(connect) 1
set SURELOG_IGNORE_CMD(connwrappers) 1
set SURELOG_IGNORE_CMD(coolrunner2_sop) 1
set SURELOG_IGNORE_CMD(copy) 1
set SURELOG_IGNORE_CMD(cover) 1
set SURELOG_IGNORE_CMD(cutpoint) 1
set SURELOG_IGNORE_CMD(debugrun) 1
set SURELOG_IGNORE_CMD(delete) 1
set SURELOG_IGNORE_CMD(deminout) 1
set SURELOG_IGNORE_CMD(design) 1
set SURELOG_IGNORE_CMD(determine_init) 1
set SURELOG_IGNORE_CMD(dff2dffe) 1
set SURELOG_IGNORE_CMD(dff2dffs) 1
set SURELOG_IGNORE_CMD(dffinit) 1
set SURELOG_IGNORE_CMD(dfflibmap) 1
set SURELOG_IGNORE_CMD(dffsr2dffconvert) 1 
set SURELOG_IGNORE_CMD(dumpprint) 1 
set SURELOG_IGNORE_CMD(echoturning) 1 
set SURELOG_IGNORE_CMD(ecp5_ffinit) 1
set SURELOG_IGNORE_CMD(edgetypeslist) 1 
set SURELOG_IGNORE_CMD(equiv_add) 1 
set SURELOG_IGNORE_CMD(equiv_induct) 1 
set SURELOG_IGNORE_CMD(equiv_make) 1 
set SURELOG_IGNORE_CMD(equiv_mar) 1 
set SURELOG_IGNORE_CMD(equiv_miter) 1 
set SURELOG_IGNORE_CMD(equiv_opt) 1 
set SURELOG_IGNORE_CMD(equiv_purge) 1
set SURELOG_IGNORE_CMD(equiv_remove) 1 
set SURELOG_IGNORE_CMD(equiv_simple) 1 
set SURELOG_IGNORE_CMD(equiv_status) 1 
set SURELOG_IGNORE_CMD(equiv_struct) 1 
set SURELOG_IGNORE_CMD(expose) 1 
set SURELOG_IGNORE_CMD(extract) 1 
set SURELOG_IGNORE_CMD(extract_counter) 1 
set SURELOG_IGNORE_CMD(extract_fafind) 1
set SURELOG_IGNORE_CMD(extract_reduce) 1 
set SURELOG_IGNORE_CMD(flatten) 1 
set SURELOG_IGNORE_CMD(flowmappack) 1 
set SURELOG_IGNORE_CMD(fmcombine) 1 
set SURELOG_IGNORE_CMD(freduceperform) 1 
set SURELOG_IGNORE_CMD(fsm) 1
set SURELOG_IGNORE_CMD(fsm_detect) 1 
set SURELOG_IGNORE_CMD(fsm_expand) 1 
set SURELOG_IGNORE_CMD(fsm_export) 1 
set SURELOG_IGNORE_CMD(fsm_extract) 1 
set SURELOG_IGNORE_CMD(fsm_info) 1 
set SURELOG_IGNORE_CMD(fsm_map) 1 
set SURELOG_IGNORE_CMD(fsm_opt) 1 
set SURELOG_IGNORE_CMD(fsm_recode) 1 
set SURELOG_IGNORE_CMD(greenpak4_dffinv) 1 
set SURELOG_IGNORE_CMD(helpdisplay) 1 
set SURELOG_IGNORE_CMD(hierarchy) 1
set SURELOG_IGNORE_CMD(hilomap) 1
set SURELOG_IGNORE_CMD(historyshow) 1
set SURELOG_IGNORE_CMD(ice40_braminit) 1
set SURELOG_IGNORE_CMD(ice40_dsp) 1
set SURELOG_IGNORE_CMD(ice40_ffinit) 1
set SURELOG_IGNORE_CMD(ice40_ffssr) 1
set SURELOG_IGNORE_CMD(ice40_opt) 1
set SURELOG_IGNORE_CMD(ice40_unlut) 1
set SURELOG_IGNORE_CMD(insbuf) 1
set SURELOG_IGNORE_CMD(iopadmap) 1
set SURELOG_IGNORE_CMD(json) 1
set SURELOG_IGNORE_CMD(log) 1
set SURELOG_IGNORE_CMD(ls) 1
set SURELOG_IGNORE_CMD(ltp) 1
set SURELOG_IGNORE_CMD(lut2mux) 1
set SURELOG_IGNORE_CMD(maccmap) 1
set SURELOG_IGNORE_CMD(memory) 1
set SURELOG_IGNORE_CMD(memory_brammap) 1
set SURELOG_IGNORE_CMD(memory_collect) 1
set SURELOG_IGNORE_CMD(memory_dff) 1
set SURELOG_IGNORE_CMD(memory_map) 1
set SURELOG_IGNORE_CMD(memory_memx) 1
set SURELOG_IGNORE_CMD(memory_nordff) 1
set SURELOG_IGNORE_CMD(memory_share) 1
set SURELOG_IGNORE_CMD(memory_unpack) 1
set SURELOG_IGNORE_CMD(miter) 1
set SURELOG_IGNORE_CMD(mutate) 1
set SURELOG_IGNORE_CMD(muxcover) 1
set SURELOG_IGNORE_CMD(muxpack) 1
set SURELOG_IGNORE_CMD(nlutmap) 1
set SURELOG_IGNORE_CMD(onehot) 1
set SURELOG_IGNORE_CMD(opt) 1
set SURELOG_IGNORE_CMD(opt_clean) 1
set SURELOG_IGNORE_CMD(opt_demorgan) 1
set SURELOG_IGNORE_CMD(opt_expr) 1
set SURELOG_IGNORE_CMD(opt_lut) 1
set SURELOG_IGNORE_CMD(opt_merge) 1
set SURELOG_IGNORE_CMD(opt_muxtree) 1
set SURELOG_IGNORE_CMD(opt_reduce) 1
set SURELOG_IGNORE_CMD(opt_rmdff) 1
set SURELOG_IGNORE_CMD(peepopt) 1
set SURELOG_IGNORE_CMD(plugin) 1
set SURELOG_IGNORE_CMD(pmux2shiftx) 1
set SURELOG_IGNORE_CMD(pmuxtree) 1
set SURELOG_IGNORE_CMD(prepgeneric) 1
set SURELOG_IGNORE_CMD(proctranslate) 1
set SURELOG_IGNORE_CMD(proc_arst) 1
set SURELOG_IGNORE_CMD(proc_clean) 1
set SURELOG_IGNORE_CMD(proc_dff) 1
set SURELOG_IGNORE_CMD(proc_dlatch) 1
set SURELOG_IGNORE_CMD(proc_init) 1
set SURELOG_IGNORE_CMD(proc_muxc) 1
set SURELOG_IGNORE_CMD(proc_rmdead) 1
set SURELOG_IGNORE_CMD(qwpquadratic) 1
set SURELOG_IGNORE_CMD(readload) 1
set SURELOG_IGNORE_CMD(read_aiger) 1
set SURELOG_IGNORE_CMD(read_blif) 1
set SURELOG_IGNORE_CMD(read_ilang) 1
set SURELOG_IGNORE_CMD(read_json) 1
set SURELOG_IGNORE_CMD(read_liberty) 1
set SURELOG_IGNORE_CMD(rename) 1
set SURELOG_IGNORE_CMD(rmports) 1
set SURELOG_IGNORE_CMD(sat) 1
set SURELOG_IGNORE_CMD(scatter) 1
set SURELOG_IGNORE_CMD(scc) 1
set SURELOG_IGNORE_CMD(select) 1
set SURELOG_IGNORE_CMD(setattr) 1
set SURELOG_IGNORE_CMD(setparam) 1
set SURELOG_IGNORE_CMD(setundef) 1
set SURELOG_IGNORE_CMD(sf2_iobs) 1
set SURELOG_IGNORE_CMD(share) 1
set SURELOG_IGNORE_CMD(shell) 1
set SURELOG_IGNORE_CMD(show) 1
set SURELOG_IGNORE_CMD(shregmap) 1
set SURELOG_IGNORE_CMD(sim) 1
set SURELOG_IGNORE_CMD(simplemap) 1
set SURELOG_IGNORE_CMD(splice) 1
set SURELOG_IGNORE_CMD(splitnetssplit) 1
set SURELOG_IGNORE_CMD(statprint) 1
set SURELOG_IGNORE_CMD(submodmoving) 1
set SURELOG_IGNORE_CMD(supercoveradd) 1
set SURELOG_IGNORE_CMD(synth) 1
set SURELOG_IGNORE_CMD(synth_achronix) 1
set SURELOG_IGNORE_CMD(synth_anlogic) 1
set SURELOG_IGNORE_CMD(synth_coolrunner2) 1
set SURELOG_IGNORE_CMD(synth_easic) 1
set SURELOG_IGNORE_CMD(synth_ecp5) 1
set SURELOG_IGNORE_CMD(synth_gowin) 1
set SURELOG_IGNORE_CMD(synth_greenpak4) 1
set SURELOG_IGNORE_CMD(synth_ice40) 1
set SURELOG_IGNORE_CMD(synth_intel) 1
set SURELOG_IGNORE_CMD(synth_sf2) 1
set SURELOG_IGNORE_CMD(synth_xilinx) 1
set SURELOG_IGNORE_CMD(tclexecute) 1
set SURELOG_IGNORE_CMD(techmap) 1
set SURELOG_IGNORE_CMD(tee) 1
set SURELOG_IGNORE_CMD(test_abcloop) 1
set SURELOG_IGNORE_CMD(test_autotb) 1
set SURELOG_IGNORE_CMD(test_cell) 1
set SURELOG_IGNORE_CMD(torder) 1
set SURELOG_IGNORE_CMD(trace) 1
set SURELOG_IGNORE_CMD(tribuf) 1
set SURELOG_IGNORE_CMD(uniquify) 1
set SURELOG_IGNORE_CMD(verific) 1
set SURELOG_IGNORE_CMD(verilog_defaults) 1
set SURELOG_IGNORE_CMD(verilog_defines) 1
set SURELOG_IGNORE_CMD(wbflip) 1
set SURELOG_IGNORE_CMD(wreduce) 1
set SURELOG_IGNORE_CMD(write_aiger) 1
set SURELOG_IGNORE_CMD(write_blif) 1
set SURELOG_IGNORE_CMD(write_btor) 1
set SURELOG_IGNORE_CMD(write_edif) 1
set SURELOG_IGNORE_CMD(write_file) 1
set SURELOG_IGNORE_CMD(write_firrtl) 1
set SURELOG_IGNORE_CMD(write_ilang) 1
set SURELOG_IGNORE_CMD(write_intersynth) 1
set SURELOG_IGNORE_CMD(write_json) 1
set SURELOG_IGNORE_CMD(write_simplec) 1
set SURELOG_IGNORE_CMD(write_smt2) 1
set SURELOG_IGNORE_CMD(write_smv) 1
set SURELOG_IGNORE_CMD(write_spice) 1
set SURELOG_IGNORE_CMD(write_table) 1
set SURELOG_IGNORE_CMD(write_verilog) 1
set SURELOG_IGNORE_CMD(zinit) 1
set SURELOG_IGNORE_CMD(yosys_proc) 1



# Yosys command
proc read_verilog { path } {
    global SURELOG_FILE_LIST
    surelog:log "read_verilog $path"
    lappend SURELOG_FILE_LIST $path
}

# Yosys command
proc script { args } {
    surelog:process_args $args
}

proc surelog:register_ignored_commands { } {
    global SURELOG_IGNORE_CMD
    foreach cmd [array names SURELOG_IGNORE_CMD] {
	eval "proc $cmd { args } { surelog:log \"> Ignoring $cmd\"}" 
    }
}

proc surelog:process_args { args } {
    if ![file exist $args] {
	surelog:log "ERROR: File \"$args\" does not exit"
	exit 0
    } else {
	surelog:log "> Converting file \"$args\""
	set fid [open "$args" "r"]
	set content [read $fid]
	close $fid
	regsub -all {\$} $content "\\$" content
	regsub -all {proc} $content "yosys_proc" content
	eval $content
	
    }
}

proc surelog:main { args } {
    surelog:log "----------------------------"
    surelog:log "SURELOG YOSYS FRONTEND BEGIN"
    surelog:log "----------------------------"
    surelog:register_ignored_commands
    surelog:process_args $args
    surelog:execute
    surelog:log "----------------------------"
    surelog:log "SURELOG YOSYS FRONTEND END"
    surelog:log "----------------------------"
}

proc surelog:execute {} {
    global SURELOG_FILE_LIST
    set cmd "surelog -mt max -parse  -writepp +incdir+.+rtl "
    append cmd $SURELOG_FILE_LIST
    surelog:log "> Executing: $cmd"
    set result [exec sh -c "[getResourceDirectory]/$cmd"]
    puts $result
}



surelog:main $argv
