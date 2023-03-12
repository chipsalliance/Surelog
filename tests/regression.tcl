#!/usr/bin/env tclsh

# Copyright 2017-2023 Alain Dargelas
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
set script_path [ file dirname [ file normalize [ info script ] ] ]
source $script_path/json.tcl
source $script_path/pdict.tcl

variable myLocation [file normalize [info script]]
set myProjetPathNoNormalize [file dirname [file dirname [info script]]]

proc project_path {} {
    variable myLocation
    return [file dirname [file dirname $myLocation]]
}

proc printHelp {} {
    puts "regression.tcl help"
    puts "regression.tcl tests=<testname>                  (Tests matching regular expression)"
    puts "               test=<testname>                   (Just that test)"
    puts "               debug=<none, valgrind, ddd>"
    puts "               build=<Debug, Release>"
    puts "               mt=<nbThreads>"
    puts "               mp=<nbProcesses>"
    puts "               large                             (large tests too)"
    puts "               show_diff                         (Shows text diff)"
    puts "               diff_mode                         (Only diff)"
    puts "regression.tcl update                            (Updates the diffs)"
    puts "regression.tcl verification                      (Equivalence checking against Yosys parser)"
    puts "               NO GATE: Both parsers didn't produce gate-level netlist"
    puts "               S GATE: Surelog parser didn't produce gate-level netlist"
    puts "               Y GATE: Yosys parser didn't produce gate-level netlist"
    puts "               INCOM: Incomplete, missing module declaration => Inconclusive"
    puts "               PASS: Formally equivalent"
    puts "               DIFF: Formally not-equivalent"
    puts "               UH PLUG: UHDM Plugin error"
    puts "               UH YGATE: UHDM Plugin error + Yosys no gate"
    puts "               MODEL EM: Empty formal model"
    puts "               MODEL ER: Error in formal model"
}

set MUTE 0
set LOG_CONTENT ""
proc log { text } {
    global LOG_FILE MUTE LOG_CONTENT
    if {$MUTE == 0} {
        puts $text
        flush stdout
    }
    if ![info exist LOG_FILE] {
        set LOG_FILE [open regression.log "w"]
    }
    puts $LOG_FILE $text
    flush $LOG_FILE
    append LOG_CONTENT "$text\n"
}

proc log_nonewline { text } {
    global LOG_FILE MUTE LOG_CONTENT
    if {$MUTE == 0} {
        puts -nonewline $text
        flush stdout
    }
    if ![info exist LOG_FILE] {
        set LOG_FILE [open regression.log "w"]
    }
    puts -nonewline $LOG_FILE $text
    flush $LOG_FILE
    append LOG_CONTENT $text
}

set UPDATE 0
set TIME "/usr/bin/env time"
set DEBUG_TOOL ""
set PRIOR_USER 0
set PRIOR_ELAPSED 0
set USER 0
set ELAPSED 0
set PRIOR_MAX_MEM 0
set MAX_MEM 0
set PRIOR_MAX_TIME 0
set MAX_TIME 0
set DEBUG "none"
set MT_MAX 0
set MP_MAX 0
set LARGE_TESTS 0
set SHOW_DIFF 0
set DIFF_MODE 0
set VERIFICATION 0
set SEARCH_DIR ""

if [regexp {show_diff}  $argv] {
    regsub "show_diff" $argv "" argv
    set SHOW_DIFF 1
}

if [regexp {mute}  $argv] {
    regsub "mute" $argv "" argv
    set MUTE 1
}

if [regexp {verification}  $argv] {
    regsub "verification" $argv "" argv
    set VERIFICATION 1
}

if [regexp {diff_mode}  $argv] {
    regsub "diff_mode" $argv "" argv
    set DIFF_MODE 1
}

if [regexp {large}  $argv] {
    set LARGE_TESTS 1
    log "Running large tests"
} else {
    log "Skipping large tests"
}

if [regexp {mt=([0-9]+)} $argv tmp MT_MAX] {
}

if [regexp {search_dir=([a-zA-Z0-9/\.-]+)} $argv tmp SEARCH_DIR] {
}

if [regexp {\{search_dir=(.*)\}} $argv tmp SEARCH_DIR] {
}

if [regexp {debug=([a-z]+)} $argv tmp DEBUG] {
    if {$DEBUG == "ddd"} {
        set DEBUG_TOOL "ddd"
    }
}

if {$argv == "help"} {
    printHelp
    exit
}

set SHELL sh
set SHELL_ARGS -c
if { ($tcl_platform(platform) == "windows") && (![info exists ::env(MSYSTEM)]) } {
    set SHELL cmd
    set SHELL_ARGS /c
    set TIME ""
    set DEBUG_TOOL ""
}

set TESTTARGET ""
set ONETEST ""
if [regexp {tests=([A-Za-z0-9_]+)} $argv tmp TESTTARGET] {
}
if [regexp {test=([A-Za-z0-9_\.]+)} $argv tmp TESTTARGET] {
    set ONETEST $TESTTARGET
}

set SHOW_DETAILS 0
if [regexp {\-details} $argv] {
    set SHOW_DETAILS 1
}

if [regexp {update} $argv] {
    set UPDATE 1
}

set COMMIT_TEXT ""
if [regexp {commit=([A-Za-z0-9_ \.]+)} $argv tmp COMMIT_TEXT] {
}

set EXE_PATH "[pwd]/bin"

set BUILD "Release"
if [regexp {build=([A-Za-z0-9_]+)} $argv tmp BUILD] {
    puts "BUILD=$BUILD"
    set EXE_PATH "[pwd]/../dbuild/bin"
}

if [regexp {path=([A-Za-z0-9_/\.\-\:]+)} $argv tmp EXE_PATH] {
}

set EXE_NAME "surelog"
set YOSYS_EXE "yosys"
set SV2V_EXE "sv2v"

if [regexp {exe_name=([A-Za-z0-9_/\.\-\:]+)} $argv tmp EXE_NAME] {
}

if [regexp {yosys_exe=([A-Za-z0-9_/\.\-\:]+)} $argv tmp YOSYS_EXE] {
}

if [regexp {sv2v_exe=([A-Za-z0-9_/\.\-\:]+)} $argv tmp SV2V_EXE] {
}

set SURELOG_VERSION "$EXE_PATH/$EXE_NAME"
set UHDM_DUMP_COMMAND "[pwd]/third_party/UHDM/bin/uhdm-dump"
#This condition is not compatible across platforms.
#if ![file exist $SURELOG_VERSION] {
#    puts "ERROR: Cannot find executable $SURELOG_VERSION!"
#    exit 1
#}

set REGRESSION_PATH [pwd]

set SURELOG_COMMAND "$TIME $DEBUG_TOOL $SURELOG_VERSION"

source [project_path]/tests/blacklisted.tcl

if [regexp {black_listed=([A-Za-z0-9_/\.\-\:]+)} $argv tmp blacklisted_file] {
    source $blacklisted_file
}

if { $tcl_platform(platform) == "windows" } {
    set BLACK_LIST $WINDOWS_BLACK_LIST
} else {
    set BLACK_LIST $UNIX_BLACK_LIST
}

proc findFiles { basedir pattern {level 0}} {

    if {$level > 3} {
        return
    }
    # Fix the directory name, this ensures the directory name is in the
    # native format for the platform and contains a final directory seperator
    set basedir [string trimright [file join [file normalize $basedir] { }]]
    set fileList {}

    # Look in the current directory for matching files, -type {f r}
    # means ony readable normal files are looked at, -nocomplain stops
    # an error being thrown if the returned list is empty
    foreach fileName [glob -nocomplain -type {f r} -path $basedir $pattern] {
        lappend fileList $fileName
    }

    # Now look for any sub direcories in the current directory
    foreach dirName [glob -nocomplain -type {d  r} -path $basedir *] {
        # Recusively call the routine on the sub directory and append any
        # new files to the results
        set subDirList [findFiles $dirName $pattern [expr $level +1]]
        if { [llength $subDirList] > 0 } {
            foreach subDirFile $subDirList {
                lappend fileList $subDirFile
            }
        }
    }
    return $fileList
}

proc findDirs { basedir pattern {level 0}} {
    if {$level > 3} {
        return
    }
    # Fix the directory name, this ensures the directory name is in the
    # native format for the platform and contains a final directory seperator
    set basedir [string trimright [file join [file normalize $basedir] { }]]
    set fileList {}

    # Look in the current directory for matching files, -type {f r}
    # means ony readable normal files are looked at, -nocomplain stops
    # an error being thrown if the returned list is empty
    foreach fileName [glob -nocomplain -type {d r} -path $basedir $pattern] {
        lappend fileList $fileName
    }

    # Now look for any sub direcories in the current directory
    foreach dirName [glob -nocomplain -type {d  r} -path $basedir *] {
        # Recusively call the routine on the sub directory and append any
        # new files to the results
        set subDirList [findDirs $dirName $pattern [expr $level +1]]
        if { [llength $subDirList] > 0 } {
            foreach subDirFile $subDirList {
                lappend fileList $subDirFile
            }
        }
    }
    return $fileList
}

proc load_tests { } {
    global TESTS TESTS_DIR LONGESTTESTNAME TESTTARGET ONETEST LARGE_TESTS LONG_TESTS MT_MAX MP_MAX BLACK_LIST
    global VERIFICATION SEARCH_DIR

    set dirs "../tests/ ../third_party/tests/"
    if {$SEARCH_DIR != ""} {
        set dirs $SEARCH_DIR
    }
    set fileLists ""
    foreach dir $dirs {
        if {$VERIFICATION == 0} {
            append fileList "[findFiles $dir *.sl] "
        } else {
            append fileList "[findFiles $dir *.slv] "
        }
    }
    set testcommand ""
    set LONGESTTESTNAME 1
    set totaltest 0
    foreach file $fileList {
        if {$VERIFICATION == 0} {
            regexp {([a-zA-Z0-9_/:-]+)/([a-zA-Z0-9_-]+)\.sl} $file tmp testdir testname
        } else {
            regexp {([a-zA-Z0-9_/:-]+)/([a-zA-Z0-9_\.-]+)\.slv} $file tmp testdir testname
       }
        regsub [pwd]/ $testdir "" testdir
        incr totaltest
        if {($TESTTARGET != "") && ![regexp $TESTTARGET $testname]} {
            continue
        }
        if {($ONETEST != "") && ($ONETEST != $testname)} {
            continue
        }
        if {($ONETEST == "") && ($LARGE_TESTS == 0)} {
            if [info exist LONG_TESTS($testname)] {
                continue
            }
        }
        if {($ONETEST == "") && [dict exists $BLACK_LIST $testname]} {
            # Ignore black listed ones
            continue
        }

        if {$LONGESTTESTNAME < [string length $testname]} {
            set LONGESTTESTNAME [string length $testname]
        }

        if {$VERIFICATION == 0} {
            set fid [open $testdir/$testname.sl]
        } else {
             set fid [open $testdir/$testname.slv]
        }
        set testcommand [read $fid]
        close $fid

        set TESTS($testname) $testcommand
        set TESTS_DIR($testname) $testdir
    }
    log "Run with mt=$MT_MAX, mp=$MP_MAX"
    log "THERE ARE $totaltest tests"
    log "RUNNING   [array size TESTS] tests"
    log ""
}

proc count_messages { result } {
    set fatals -1
    set errors -1
    set warnings -1
    set notes -1
    set syntax -1

    # Diff test
    if [regexp {\| FATAL \|[ ]*([0-9]+)[ ]*\|[ ]*([0-9]+)[ ]*} $result tmp fatal1 fatal2] {
        set fatals [expr $fatal1 + $fatal2]
    }
    if [regexp {\|SYNTAX \|[ ]*([0-9]+)[ ]*\|[ ]*([0-9]+)[ ]*} $result tmp syntax1 syntax2] {
        set syntax [expr $syntax1 + $syntax2]
    }
    if [regexp {\| ERROR \|[ ]*([0-9]+)[ ]*\|[ ]*([0-9]+)[ ]*} $result tmp error1 error2] {
        set errors [expr $error1 + $error2]
    }
    if [regexp {\|WARNING\|[ ]*([0-9]+)[ ]*\|[ ]*([0-9]+)[ ]*} $result tmp warning1 warning2] {
        set warnings [expr $warning1 + $warning2]
    }
    if [regexp {\| NOTE  \|[ ]*([0-9]+)[ ]*\|[ ]*([0-9]+)[ ]*} $result tmp note1 note2] {
        set notes [expr $note1 + $note2]
    }

    # Show help test
    if [regexp {outputlineinfo} $result] {
        set fatals 0
        set syntax 0
        set errors 0
        set warnings 0
        set notes 0
    }
    # stats per message ID

    set lines [split $result "\n"]
    foreach line $lines {
        # Normal test
        regexp {FATAL\] : ([0-9]+)} $line tmp fatals
        regexp {SYNTAX\] : ([0-9]+)} $line tmp syntax
        regexp {ERROR\] : ([0-9]+)} $line tmp errors
        regexp {WARNING\] : ([0-9]+)} $line tmp warnings
        regexp {NOTE\] : ([0-9]+)} $line tmp notes

        if [regexp {(\[.*\])} $line tmp code] {
            if [info exist CODES($code)] {
                incr CODES($code)
            } else {
                set CODES($code) 1
            }
        }
    }

    foreach line $lines {
        # Diff UHDM Dump lines
        if [regexp {^[ ]*[|\\]} $line] {
            incr notes
        }

        # A few that can be safely ignored
        if {[string first ": Cannot open include file \"/dev/null\"." $line] != -1} {
            incr errors -1
        }
    }

    set details ""
    foreach name [lsort -dictionary [array names CODES]] {
        lappend details [list $name $CODES($name)]
    }

    return [list $fatals $errors $warnings $notes $details $syntax]
}

proc count_split { string } {
    return [llength [split $string /]]
}

proc initialize_reg { file } {
    if ![file exists $file] {
        return
    }
    set fid [open $file]
    set content [read $fid]
    close $fid
    regsub -all {1'hx} $content "1'h0" content
    regsub -all {\(\* src = \"[a-zA-Z0-9_/|:\.-]*\" \*\)} $content "" content
    regsub -all {\(\* keep =  1  \*\)\n} $content "" content
    set fid [open $file "w"]
    puts $fid $content
    close $fid
}

# Equivalence checking in between Yosys parser and Surelog parser
proc formal_verification { command testname } {
    global env SHELL SHELL_ARGS YOSYS_EXE SV2V_EXE TIME
    set yosys_command ""
    set output_dir ""
    set directory ""
    for {set i 0} {$i < [llength $command]} {incr i} {
        set token [lindex $command $i]
        if {$token == "-o"} {
            incr i
            set token [lindex $command $i]
            set output_dir $token
            continue
        }
        if {$token == "tb.v"} {
            continue
        }
        if [file exist $token] {
            set directory [file dirname $token]
            append yosys_command "$token "
        }
    }
    set top_module ""
    set surelog_param_command ""
    
    set search_modules ""
    if [regexp {/src} [pwd]] {
        set search_modules "-y $directory +libext+.v+.sv"
        set yosys_command ""
        set dir [file dirname [pwd]]
        set json [findFiles $dir "*.json"]
        set fid [open $json]
        set content [read $fid]
        close $fid
        set di [json::json2dict $content]
        #pdict $di
        set design_name ""
        set filelist ""
        set parameters ""
        set gate_design_dir ""
        dict for {key val} $di {
            if {$key == "design_name"} {
                set design_name $val
                set gate_design_dir $design_name
            } elseif {$key == "filelist"} {
                set filelist $val
                foreach file $filelist {
                    append yosys_command "[file tail $file] "
                }
            } elseif {$key == "run_config"} {
                set configs $val
                foreach config $configs {
                    dict for {key val} $config {
                        if {$key == "parameters"} {
                            set parameters $val
                            foreach param $parameters {
                                append surelog_param_command "-P$param "
                                regsub {=} $param "_" param
                                append gate_design_dir "_$param"
                            }
                        }
                    }
                    # stop at the first config
                    break
                }
            }
        }
        set f [open $output_dir/yosys.out "w"]
        close $f
    }
    # Surelog parser
    set yid [open "$output_dir/surelog.ys" "w"]
    puts $yid "plugin -i systemverilog"
    puts $yid "tee -o $output_dir/surelog_ast.txt read_systemverilog -dump_ast1 -mutestdout $search_modules $surelog_param_command $yosys_command"
    puts $yid "hierarchy -auto-top"
    puts $yid "synth"    
    puts $yid "write_verilog  $output_dir/surelog_gate.v"
    close $yid
    set surelog_parse ""
    catch {set out [exec $YOSYS_EXE -s "$output_dir/surelog.ys" -q -q -l $output_dir/surelog.out]} surelog_parse
    initialize_reg $output_dir/surelog_gate.v
    
    if [regexp {/src} [pwd]] {
        set yosys_parse ""
        if [file exists $dir/$gate_design_dir/top.v] {
            file copy -force $dir/$gate_design_dir/top.v $output_dir/yosys_gate.v
        } else {
            set yosys_parse "NO FILE"
        }
    } else {
        # Yosys parser
        set yid [open "$output_dir/yosys.ys" "w"]
        puts $yid "tee -o $output_dir/yosys_ast.txt read_verilog -dump_ast1 -sv $yosys_command"
        puts $yid "hierarchy -auto-top"
        puts $yid "synth"    
        puts $yid "write_verilog $output_dir/yosys_gate.v"
        close $yid
        set yosys_parse ""
        catch {set out [exec $YOSYS_EXE -s "$output_dir/yosys.ys"  -q -q -l $output_dir/yosys.out]} yosys_parse
        initialize_reg $output_dir/yosys_gate.v
        
        # If Yosys parser fails, try again with SV2V
        if [regexp {ERROR:} $yosys_parse] {
            catch {set out [exec $SV2V_EXE [lindex $yosys_command 0] -w=$output_dir/sv2v.v]} yosys_parse
            set yid [open "$output_dir/yosys.ys" "w"]
            if [file exist $output_dir/sv2v.v] {
                exec sh -c "sed -i 's/\"inv\"/4/g' $output_dir/sv2v.v"
            }
            puts $yid "tee -o $output_dir/yosys_ast.txt read_verilog -dump_ast1 $output_dir/sv2v.v"
            puts $yid "hierarchy -auto-top"
            puts $yid "synth"    
            puts $yid "write_verilog $output_dir/yosys_gate.v"
            close $yid
            set yosys_parse ""
            catch {set out [exec $YOSYS_EXE -s "$output_dir/yosys.ys"  -q -q -l $output_dir/yosys.out]} yosys_parse
            initialize_reg $output_dir/yosys_gate.v
            
        }
    }
    
    if [file exist "$output_dir/surelog.out"] {
        set fid [open "$output_dir/surelog.out"]
        set content [read $fid]
        set topmodule ""
        regexp {Top module:  \\([a-zA-Z0-9_-]*)} $content tmp topmodule
        close $fid
    }
    # Find cell libraries
    set yosys_path "$env(HOME)/yosys"
    set cells_sim $yosys_path/share/xilinx/cells_sim.v
    set cells_xtra $yosys_path/share/xilinx/cells_xtra.v
    if [file exist [file dirname $YOSYS_EXE]/../share/yosys/xilinx/cells_sim.v] {
        set yosys_path [file dirname $YOSYS_EXE]/..
        set cells_sim $yosys_path/share/yosys/xilinx/cells_sim.v
        set cells_xtra $yosys_path/share/yosys/xilinx/cells_xtra.v
    }
    # Equivalence checking
    if {($surelog_parse == "") && ($yosys_parse == "")} {
        set diff ""
        catch {set diff [exec $SHELL $SHELL_ARGS "diff $output_dir/surelog_gate.v $output_dir/yosys_gate.v"]} diff
        if {$diff == ""} {
            return [list "EQUIVALENT" ""] 
        }
        set yid [open "$output_dir/equiv.ys" "w"]
        puts $yid "read_verilog $output_dir/surelog_gate.v $cells_sim $cells_xtra"
        puts $yid "prep -flatten -top $topmodule"
        puts $yid "splitnets -ports;;"
        puts $yid "design -stash surelog"
        puts $yid "read_verilog $output_dir/yosys_gate.v $cells_sim $cells_xtra"
        puts $yid "splitnets -ports;;"
        puts $yid "prep -flatten -top $topmodule"
        puts $yid "design -stash yosys"
        puts $yid "design -copy-from surelog -as surelog $topmodule"
        puts $yid "design -copy-from yosys -as yosys $topmodule"
        puts $yid "equiv_make surelog yosys equiv"
        puts $yid "prep -flatten -top equiv"

        puts $yid "opt_clean -purge"
        #puts $yid "show -prefix equiv-prep -colors 1 -stretch"

        puts $yid "opt -full"
        puts $yid "equiv_simple -seq 5"
        puts $yid "equiv_induct -seq 5"
        puts $yid "equiv_status -assert"
        close $yid
        set equiv_run ""
        catch {exec $SHELL $SHELL_ARGS "$TIME $YOSYS_EXE -s $output_dir/equiv.ys -q -q -l $output_dir/equiv.out"}  equiv_run
        set proven 0
        set unproven 0
        if [file exist "$output_dir/equiv.out"] {
            set fid [open "$output_dir/equiv.out"]
            set content [read $fid]
            close $fid
            if [regexp {Equivalence successfully proven} $content] {
                set proven 1
            } elseif {[regexp {Unproven} $content] || [regexp {[0-9]+ unproven} $content]} {
                set unproven 1
            } elseif [regexp {ERROR: Can't find gold module surelog} $content] {
                return [list "INVALID_MODEL_SURELOG" $equiv_run]
            } elseif [regexp {ERROR: Can't find gate module yosys} $content] {
                return [list "INVALID_MODEL_YOSYS" $equiv_run]
            } elseif [regexp {Proved 0 previously unproven \$equiv cells\.} $content] {
                return [list "EMPTY_MODEL" $equiv_run] 
            } elseif [regexp {ERROR:} $content] {
                return [list "ERROR_MODEL" ""] 
            }  
        }
        if {$proven} {
            return [list "EQUIVALENT" $equiv_run] 
        }
        if {$unproven} {
            return [list "NOT_EQUIVALENT" $equiv_run]  
        }
    }
    return [list "INCONCLUSIVE" ""] 
}

proc run_regression { } {
    global TESTS TESTS_DIR SURELOG_COMMAND UHDM_DUMP_COMMAND LONGESTTESTNAME TESTTARGET ONETEST UPDATE USER ELAPSED PRIOR_USER PRIOR_ELAPSED MUTE TIME DEBUG
    global DIFF_TESTS PRIOR_MAX_MEM MAX_MEM MAX_TIME PRIOR_MAX_TIME SHOW_DETAILS MT_MAX MP_MAX REGRESSION_PATH LARGE_TESTS LONG_TESTS DIFF_MODE SHELL SHELL_ARGS
    global VERIFICATION STATUS_STATS STATUS_TESTS
    set overrallpass "PASS"

    set w1 $LONGESTTESTNAME
    set w2 8
    set w4 8
    set w3 18
    set w5 8
    set w6 6
    set w7 9
    set MEM 0
    set sep +-[string repeat - $w1]-+-[string repeat - $w2]-+-[string repeat - $w6]-+-[string repeat - $w4]-+-[string repeat - $w2]-+-[string repeat - $w4]-+-[string repeat - $w7]-+-[string repeat - $w5]-+-[string repeat - $w5]-+
    log $sep
    log [format "| %-*s | %-*s | %*s | %*s | %*s | %*s | %*s | %*s | %*s |" $w1 "TESTNAME" $w2 "STATUS" $w6 "FATAL"  $w2 "SYNTAX" $w4 "ERROR" $w2 "WARNING"  $w7 "NOTE-UHDM"  $w5 "TIME" $w5 "MEM(Mb)"]
    log $sep

    if {$UPDATE == 1} {
        if {$VERIFICATION == 1} {
            if [file exist $REGRESSION_PATH/tests/formal_status.tcl] {
                if [file exist $REGRESSION_PATH/../formal/formal_status.tcl] {
                    source $REGRESSION_PATH/../formal/formal_status.tcl
                }
                source $REGRESSION_PATH/tests/formal_status.tcl
                set fidStatus [open $REGRESSION_PATH/../formal/formal_status.tcl "w"]
                foreach item [array names LOG_STATUS_TESTS] {
                    puts $fidStatus "set LOG_STATUS_TESTS($item) \"$LOG_STATUS_TESTS($item)\""
                }
                close $fidStatus
                puts "Updated Formal status for [array size LOG_STATUS_TESTS] tests."
                exit 0
            }
        }
        return ""
    }
    if {$VERIFICATION == 1} {
        if [file exist $REGRESSION_PATH/../formal/formal_status.tcl] {
            source $REGRESSION_PATH/../formal/formal_status.tcl
        }
    }
    
    foreach testname [lsort -dictionary [array names TESTS]] {
        set time_result ""
        set result ""
        if {($ONETEST != "") && ($testname != $ONETEST)} {
            continue
        }

        if {($ONETEST == "") && ($LARGE_TESTS == 0)} {
            if [info exist LONG_TESTS($testname)] {
                continue
            }
        }

        set testdir $TESTS_DIR($testname)
        file mkdir $REGRESSION_PATH/tests/$testname
        set test $testname
        set command $TESTS($testname)
        regsub -all {\\} $command "" command
        regsub -all {\n} $command " " command
        if [regexp {third_party} $testdir] {
            regsub -all {[\./]+UVM} $command "../../UVM" command
        } else {
            if ![regexp {third_party} $command] {
                regsub -all {[\./]+UVM} $command "../../third_party/UVM" command
            }
        }
        if {($ONETEST != "")} {
            log "\ncd $testdir"
            if [regexp {\.sh} $command] {
                log "$command [lindex $SURELOG_COMMAND end]\n"
            } else {
                log "$SURELOG_COMMAND $command\n"
            }
        }
        if [file exists "$REGRESSION_PATH/tests/$test/valgrind.log"] {
            file delete -force "$REGRESSION_PATH/tests/$test/valgrind.log"
        }
        if {$UPDATE == 1} {
            if {$VERIFICATION == 0} {
                if [file exist "$REGRESSION_PATH/tests/$test/${testname}.log"] {
                    log  [format "| %-*s | Copying $REGRESSION_PATH/tests/$test/${testname}.log to $testdir/${testname}.log" $w1 $testname]
                    
                    set fid [open "$REGRESSION_PATH/tests/$test/${testname}.log" "r"]
                    set content [read $fid]
                    close $fid
                    # Canonicalize things that should be neutral in diff outputs
                    regsub -all {[a-zA-Z_/-]*/Surelog/} $content {${SURELOG_DIR}/} content
                    regsub -all {[0-9]+\.[0-9]{3}([0-9]{3})?s?} $content {t.ttts} content
                    set outfd [open "$testdir/${testname}.log" "w"]
                    puts -nonewline $outfd $content
                    close $outfd
                    continue
                } else {
                    log  [format "| %-*s | No action" $w1 $testname]
                    continue
                }
            }
        }

        log_nonewline [format "| %-*s |" $w1 $testname]

        cd $testdir
        if {$DIFF_MODE == 0} {
            foreach f [findDirs $REGRESSION_PATH/tests/$test slpp_*] {
                file delete -force $f
            }
            foreach f [findDirs $testdir slpp_*] {
                file delete -force $f
            }
        }
        set passstatus "PASS"
        set verification_result ""
        if {$DIFF_MODE == 0} {
            set path [file dirname $REGRESSION_PATH]
            regsub -all $path $testdir "" path
            set count [count_split $path]
            set root ""
            for {set i 0} {$i < $count -1} {incr i} {
                append root "../"
            }
            set output_path "-o ${root}build/tests/$test/"
            if [regexp {\.sh} $command] {
                catch {set time_result [exec $SHELL $SHELL_ARGS "$TIME $command [lindex $SURELOG_COMMAND end] > $REGRESSION_PATH/tests/$test/${testname}.log"]} time_result
            } else {
                if [regexp {\*/\*\.v} $command] {
                    regsub -all {[\*/]+\*\.v} $command "" command
                    set command "$command [findFiles . *.v]"
                    regsub -all [pwd]/ $command "" command
                }
                if [regexp {\*/\*\.sv} $command] {
                    regsub -all {[\*/]+\*\.sv} $command "" command
                    set command "$command [findFiles . *.sv]"
                    regsub -all [pwd]/ $command "" command
                }
                regsub -all {\-mt[ ]+max} $command "" command
                regsub -all {\-mt[ ]+[0-9]+} $command "" command
                if {$MP_MAX > 0} {
                    regsub -all {\-nocache} $command "" command
                }
                if [regexp {\-lowmem} $command] {
                    set MP_MAX 1
                }
                set command "$command -mt $MT_MAX -mp $MP_MAX $output_path"

                if {($ONETEST != "") && ($testname != $ONETEST)} {
                    continue
                }
                set FINAL_COMMAND $SURELOG_COMMAND
                if {$DEBUG == "valgrind"} {
                    set surelog [lindex $SURELOG_COMMAND end]
                    set FINAL_COMMAND "$TIME valgrind --tool=memcheck --log-file=$REGRESSION_PATH/tests/$test/valgrind.log $surelog"
                    puts "\n$FINAL_COMMAND\n"
                }

                if {$VERIFICATION == 0} {
                    catch {set time_result [exec $SHELL $SHELL_ARGS "$FINAL_COMMAND $command > $REGRESSION_PATH/tests/$test/${testname}.log"]} time_result

                    if [file exist $REGRESSION_PATH/tests/$test/slpp_all/surelog.uhdm] {
                        if [catch {exec $SHELL $SHELL_ARGS "$UHDM_DUMP_COMMAND $REGRESSION_PATH/tests/$test/slpp_all/surelog.uhdm > $REGRESSION_PATH/tests/$test/uhdm.dump"}] {
                            set passstatus "FAILDUMP"
                            set overrallpass "FAIL"
                        }
                    } elseif [file exist $REGRESSION_PATH/tests/$test/slpp_unit/surelog.uhdm] {
                        if [catch {exec $SHELL $SHELL_ARGS "$UHDM_DUMP_COMMAND $REGRESSION_PATH/tests/$test/slpp_unit/surelog.uhdm > $REGRESSION_PATH/tests/$test/uhdm.dump"}] {
                            set passstatus "FAILDUMP"
                            set overrallpass "FAIL"
                        }
                    }
                } else {
                    set time_result ""
                    set fid [open "$REGRESSION_PATH/tests/$test/${testname}.log" "w"]
                    puts $fid "\[  FATAL\] : 0"
                    puts $fid "\[ SYNTAX\] : 0"
                    puts $fid "\[WARNING\] : 0"
                    puts $fid "\[  ERROR\] : 0"
                    puts $fid "\[   NOTE\] : 0"


                    close $fid
                    set verification_result [formal_verification $command $testname]
                    set time_result [lindex $verification_result 1]
                    set verification_result [lindex $verification_result 0]
                }
            }
        }

        if [file exists "$REGRESSION_PATH/tests/$test/${testname}.log"] {
            set fid [open "$REGRESSION_PATH/tests/$test/${testname}.log" "r"]
            set result [read $fid]
            close $fid
            regsub -all {[a-zA-Z_/-]*/Surelog/} $result {${SURELOG_DIR}/} result
            regsub -all {[0-9]+\.[0-9]{3}([0-9]{3})?s?} $result {t.ttts} result
        } else {
            if [file exists "${testname}.log"] {
                set fid [open "${testname}.log" "r"]
                set result [read $fid]
                close $fid
            }
        }

        set segfault 0
        if {$DIFF_MODE == 0} {
            if [regexp {Segmentation fault} $result] {
                set segfault 1
                foreach f [findDirs $REGRESSION_PATH/tests/$test slpp_*] {
                    file delete -force $f
                }
                foreach f [findDirs $testdir slpp_*] {
                    file delete -force $f
                }
                if [regexp {\.sh} $command] {
                    catch {set time_result [exec $SHELL $SHELL_ARGS "$TIME $command [lindex $SURELOG_COMMAND end] > $REGRESSION_PATH/tests/$test/${testname}.log"]} time_result
                } else {
                    catch {set time_result [exec $SHELL $SHELL_ARGS "$SURELOG_COMMAND $command > $REGRESSION_PATH/tests/$test/${testname}.log"]} time_result
                }
                if [regexp {Segmentation fault} $result] {
                    set passstatus "FAIL"
                    set overrallpass "FAIL"
                    set segfault 2
                } else {
                    set segfault 0
                }
            }
        }
        if [regexp {AdvancedDebug} $SURELOG_COMMAND] {
            log $result
        }

        set fatals -1
        set syntax -1
        set errors -1
        set warnings -1
        set notes -1

        set log_fatals -1
        set log_syntax -1
        set log_errors -1
        set log_warnings -1
        set log_notes -1
        set user 0
        set elapsed_min 0
        set elapsed 0
        set cpu 0
        foreach {fatals errors warnings notes details syntax} [count_messages $result] {}
        if {$VERIFICATION} {
            set log_fatals $fatals
            set log_syntax $syntax
            set log_errors $errors
            set log_warnings $warnings
            set log_notes $notes
        }
        if [regexp {([0-9\.:]+)user [0-9\.:]+system ([0-9]+):([0-9\.]+)elapsed ([0-9]+)%CPU} $time_result tmp user elapsed_min elapsed cpu] {
            set user [expr int($user)]
            set elapsed [expr int(($elapsed_min *60) + $elapsed)]
            set USER    [expr $USER + $user]
            set ELAPSED [expr $ELAPSED + $elapsed]
            if {$MAX_TIME < $elapsed} {
                set MAX_TIME $elapsed
            }
        }
        set mem 0
        if [regexp {([0-9]+)maxresident} $time_result tmp mem] {
            set mem [expr $mem / 1024]
            if {$MAX_MEM < $mem} {
                set MAX_MEM $mem
            }
        }

        set SPEED ""
        set FASTER_OR_SLOWER 0
        set DIFF_MEM 0

        set time_content ""
        set no_previous_time_content 1
        if [file exists "$REGRESSION_PATH/tests/$test/${testname}.time"] {
            set fid [open "$REGRESSION_PATH/tests/$test/${testname}.time" "r"]
            set time_content [read $fid]
            close $fid
            set no_previous_time_content 0
        }
        if [file exists "$testname.log"] {
            set fid [open "$testname.log" "r"]
            set content [read $fid]
            close $fid
            foreach {log_fatals log_errors log_warnings log_notes log_details log_syntax} [count_messages $content] {}
        }
        
        set prior_user 0
        set prior_elapsed_min 0
        set prior_elapsed 0
        set cpu 0
        regexp {([0-9\.]+)user [0-9\.:]+system ([0-9]+):([0-9\.]+)elapsed ([0-9]+)%CPU} $time_content tmp prior_user prior_elapsed_min prior_elapsed cpu
        set prior_user [expr int($prior_user)]
        set prior_elapsed [expr int(($prior_elapsed_min *60) + $prior_elapsed)]
        set PRIOR_USER    [expr $PRIOR_USER + $prior_user]
        set PRIOR_ELAPSED [expr $PRIOR_ELAPSED +  $prior_elapsed]
        if {$PRIOR_MAX_TIME < $prior_elapsed} {
            set PRIOR_MAX_TIME $prior_elapsed
        }
        if {($DIFF_MODE == 1) || ($VERIFICATION == 1)} {
            set SPEED [format "%*s " 4 "${prior_elapsed}s"]
            set FASTER_OR_SLOWER 1
        } elseif [expr ($elapsed > $prior_elapsed) && ($no_previous_time_content == 0)] {
            set SPEED [format "%*s %*s " 3 "${elapsed}s" 3 "+[expr $elapsed - $prior_elapsed]"]
                set FASTER_OR_SLOWER 1
        } elseif [expr ($elapsed == $prior_elapsed) || ($no_previous_time_content)] {
            set SPEED [format "%*s " 4 "${elapsed}s"]
        } else {
            set SPEED [format "%*s %*s " 3 "${elapsed}s" 3 "-[expr $prior_elapsed - $elapsed]"]
            set FASTER_OR_SLOWER 1
        }
        
        set prior_mem 0
        regexp {([0-9]+)maxresident} $time_content tmp prior_mem
        set prior_mem [expr $prior_mem / 1024]
        if {$PRIOR_MAX_MEM < $prior_mem} {
            set PRIOR_MAX_MEM $prior_mem
        }
        if {($DIFF_MODE == 1) || ($VERIFICATION == 1)} {
            set MEM [format "%*s " 4 "${prior_mem}"]
        } elseif [expr ($mem > $prior_mem) && ($no_previous_time_content == 0)] {
            set MEM  [format "%*s %*s " 3 "${mem}" 3 "+[expr $mem - $prior_mem]"]
            set DIFF_MEM 1
        } elseif  [expr ($mem == $prior_mem) || ($no_previous_time_content)] {
            set MEM [format "%*s " 4 "${mem}"]
        } else {
            set MEM  [format "%*s %*s " 3 "${mem}" 3 "-[expr $prior_mem - $mem]"]
            set DIFF_MEM 1
        }
        
        if {($fatals != $log_fatals) || ($errors != $log_errors) || ($warnings != $log_warnings) || ($notes != $log_notes) || ($syntax != $log_syntax)} {
            set overrallpass "DIFF"
            set passstatus "DIFF"
            set DIFF_TESTS($testname) $test
            if {$fatals != $log_fatals} {
                set fatals "$fatals ([expr $fatals - $log_fatals])"
            }
            if {$errors != $log_errors} {
                set errors "$errors ([expr $errors - $log_errors])"
            }
            if {$warnings != $log_warnings} {
                set warnings "$warnings ([expr $warnings - $log_warnings])"
            }
            if {$notes != $log_notes} {
                set notes "$notes ([expr $notes - $log_notes])"
            }
            if {$syntax != $log_syntax} {
                set syntax "$syntax ([expr $syntax - $log_syntax])"
            }
        }
        

        if [file exists "$REGRESSION_PATH/tests/$test/valgrind.log"] {
            set fid [open "$REGRESSION_PATH/tests/$test/valgrind.log" "r"]
            set valgrind_content [read $fid]
            close $fid
            if ![regexp {ERROR SUMMARY: 0} $valgrind_content] {
                incr fatals
                set fatals "$fatals ([expr $fatals - $log_fatals])"
                set passstatus "FAIL"
                set overrallpass "FAIL"
            }
        }

        if {$verification_result == "EQUIVALENT"} {
            set passstatus "PASS"
        } elseif {$verification_result == "NOT_EQUIVALENT"} {
            set passstatus "DIFF"
        } elseif {$verification_result == "INVALID_MODEL_SURELOG"} {
            set passstatus "S GATE"
        } elseif {$verification_result == "INVALID_MODEL_YOSYS"} {
            set passstatus "Y GATE"
        } elseif {$verification_result == "EMPTY_MODEL"} {
            set passstatus "MODEL EM"
        } elseif {$verification_result == "ERROR_MODEL"} {
            set passstatus "MODEL ER"
        } elseif {$verification_result == "INCONCLUSIVE"} {
            set passstatus "   "
            set fid [open "$REGRESSION_PATH/tests/$test/surelog.out" "r"]
            set result [read $fid]
            close $fid
            if [regexp {Nb undefined modules: [1-9][0-9]*} $result] {
                set passstatus "INCOM"
            }           
            if ![regexp {Dumping module } $result] {
                set passstatus "S GATE"
            }
            set fid [open "$REGRESSION_PATH/tests/$test/surelog.out" "r"]
            set surelog [read $fid]
            close $fid
            foreach line [split $surelog "\n"] {
                if [regexp {^ERROR: } $line] {
                    set passstatus "UH PLUG"
                }
            }
            set fid [open "$REGRESSION_PATH/tests/$test/yosys.out" "r"]
            set yosys [read $fid]
            close $fid
            if ![regexp {Dumping module } $yosys] {
                if {$passstatus == "S GATE"} {
                    set passstatus "NO GATE"
                } elseif {$passstatus == "UH PLUG"} {
                   set passstatus "UH YGATE" 
                } else {
                    set passstatus "Y GATE"
                }
            }
        } 
        
        if {($fatals == -1) || ($errors == -1) || ($warnings == -1) || ($notes == -1)} {
            if {$segfault == 0} {
                set segfault 1
            }
            set fatals "SEGFAULT"
            set passstatus "FAIL"
            set overrallpass "FAIL"
        }
        if {$segfault == 1 || $segfault == 2} {
            set fatals "SEGFAULT"
        }

        if [info exist STATUS_STATS($passstatus)] {
            set STATUS_STATS($passstatus) [expr $STATUS_STATS($passstatus) + 1]
        } else {
            set STATUS_STATS($passstatus) 1
        }
        set STATUS_TESTS($test) $passstatus
        if [info exist LOG_STATUS_TESTS($test)] {
            set previous_status $LOG_STATUS_TESTS($test)
            if {$previous_status == "PASS"} {
                if {$passstatus != "PASS"} {
                    puts "REGRESS $test (PASS -> $passstatus)"
                }
            } else {
                if {$passstatus == "PASS"} {
                    puts "FIXED $test ($passstatus -> PASS)"
                } else {
                    if {$previous_status != $passstatus} {
                        puts "CHANGED $test ($previous_status -> $passstatus)"
                    }
                }
            }
        }
        
        log [format " %-*s | %*s | %*s | %*s | %*s | %*s | %*s | %*s |" $w2 $passstatus $w6 $fatals $w2 $syntax $w4 $errors $w2 $warnings $w7 $notes $w5 $SPEED $w5 $MEM ]
        flush stdout
        if {$SHOW_DETAILS == 1} {
            log "Log:\n"
            foreach de $details {
                log $de
            }
            log "Diff Log:\n"
            foreach de $log_details {
                log $de
            }

        }

        set fid 0
        set fid_t 0
        if {$DIFF_MODE == 0} {
            if {$UPDATE == 1} {
                set fid [open "$testname.log" "w"]
            } else {
                set fid [open "$REGRESSION_PATH/tests/$test/${testname}.log" "w"]
                set fid_t [open "$REGRESSION_PATH/tests/$test/${testname}.time" "w"]
                puts $fid_t $time_result
                close $fid_t
            }
            puts $fid $result
            close $fid
        }

        if {($DIFF_MODE == 0) && ($passstatus == "PASS")} {
            foreach f [findDirs $REGRESSION_PATH/tests/$test slpp_*] {
                file delete -force $f
            }
            foreach f [findDirs $testdir slpp_*] {
                file delete -force $f
            }
            file delete -force uhdm.dump
            file delete -force $REGRESSION_PATH/tests/$test/uhdm.dump
            file delete -force $testdir/uhdm.dump
        }
        if {$VERIFICATION == 0} {
            cd $REGRESSION_PATH/tests
        } else {
            cd $REGRESSION_PATH
        }
    }
    log $sep
    log ""
    foreach item [array names STATUS_STATS] {
        log " $item : $STATUS_STATS($item)"
    }

    set fidStatus [open $REGRESSION_PATH/tests/formal_status.tcl "w"]
    foreach item [array names STATUS_TESTS] {
        puts $fidStatus "set LOG_STATUS_TESTS($item) \"$STATUS_TESTS($item)\""
    }
    close $fidStatus
    return $overrallpass
}


log "************************"
log "START SURELOG REGRESSION"
log ""
set systemTime [clock seconds]
set date "Starts on [clock format $systemTime -format %D] [clock format $systemTime -format %H:%M:%S]"
log "$date"
log "COMMAND: $SURELOG_COMMAND"

load_tests
set result [run_regression]

log "\n RESULT : $result\n"

if {$COMMIT_TEXT != ""} {
    if {($result == "PASS") && ($ONETEST == "") && ($TESTTARGET =="")} {
        log "git commit -m \"$COMMIT_TEXT\""
        exec sh -c "cd ~/surelog; git commit . -m \"$COMMIT_TEXT\""
        exec sh -c "git push"
    } else {
        log "CANNOT COMMIT CHANGES: $COMMIT_TEXT"
    }
    log ""
}

cd $REGRESSION_PATH

foreach testname [lsort -dictionary [array names DIFF_TESTS]] {
    set testdir $TESTS_DIR($testname)
    if {$SHOW_DIFF == 0} {
        log " tkdiff $testdir/${testname}.log $REGRESSION_PATH/tests/$DIFF_TESTS($testname)/${testname}.log"
    } else {
        log "============================== DIFF ======================================================"
        log "diff $testdir/${testname}.log $REGRESSION_PATH/tests/$DIFF_TESTS($testname)/${testname}.log"
        catch {exec $SHELL $SHELL_ARGS "diff -d $testdir/${testname}.log $REGRESSION_PATH/tests/$DIFF_TESTS($testname)/${testname}.log"} dummy
        set lines [split $dummy "\n"]
        set count 0
        foreach line $lines {
            puts $line
            incr count
            if {$count > 100} {
                puts "......"
                break
            }
        }
    }
}
if [info exists DIFF_TESTS] {
    log ""
}

set w1 8
set sep +-[string repeat - 12]-+-[string repeat - $w1]-+-[string repeat - $w1]-+
log $sep
log  [format "|              | %-*s | %-*s |" $w1 "CURRENT"  $w1  "PREVIOUS" ]
log $sep
log  [format "|TOTAL ELAPSED | %-*s | %-*s |" $w1 "${ELAPSED}s"   $w1 "${PRIOR_ELAPSED}s" ]
log  [format "|TOTAL USER    | %-*s | %-*s |" $w1 "${USER}s"      $w1 "${PRIOR_USER}s"]
log  [format "|MAX MEM TEST  | %-*s | %-*s |" $w1 "${MAX_MEM}Mb"  $w1 "${PRIOR_MAX_MEM}Mb"]
log  [format "|MAX TIME TEST | %-*s | %-*s |" $w1 "${MAX_TIME}s"  $w1 "${PRIOR_MAX_TIME}s"]
log $sep
log ""
set systemTime [clock seconds]
set date "End on [clock format $systemTime -format %D] [clock format $systemTime -format %H:%M:%S]"
log "$date"
log  "END SURELOG REGRESSION"
log "************************"

if {$DIFF_MODE == 1} {
    log  "END DIFF_MODE SURELOG REGRESSION"
}

if {$result == "PASS"} {
    exit 0
} else {
    if {$MUTE != 0} {
        puts $LOG_CONTENT
        if {($SHOW_DIFF == 1) || ($DEBUG == "valgrind")} {
            # Only return non-0 in the reporting pass, not while being run with cmake in parallel
            if {$result != "PASS"} {
                exit 1
            }
        }
    }
}

exit 0
