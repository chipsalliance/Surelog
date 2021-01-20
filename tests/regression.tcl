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
    puts "regression.tcl update (Updates the diffs)"
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
set TIME "time"
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


if [regexp {show_diff}  $argv] {
    regsub "show_diff" $argv "" argv
    set SHOW_DIFF 1
}

if [regexp {mute}  $argv] {
    regsub "mite" $argv "" argv
    set MUTE 1
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

if [regexp {mp=([0-9]+)} $argv tmp MP_MAX] {
}

if [regexp {debug=([a-z]+)} $argv tmp DEBUG] {
    if {$DEBUG == "valgrind"} {
        set DEBUG_TOOL "valgrind --tool=memcheck --log-file=valgrind.log"
    }
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
if [regexp {test=([A-Za-z0-9_]+)} $argv tmp TESTTARGET] {
    set ONETEST $TESTTARGET
}

set BUILD "Release"
if [regexp {build=([A-Za-z0-9_]+)} $argv tmp BUILD] {
    puts "BUILD=$BUILD"
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

if [regexp {path=([A-Za-z0-9_/\.\-\:]+)} $argv tmp EXE_PATH] {
}

set SURELOG_VERSION "$EXE_PATH/surelog"
set UHDM_DUMP_COMMAND "[pwd]/third_party/UHDM/bin/uhdm-dump"
#This condition is not compatible across platforms. 
#if ![file exist $SURELOG_VERSION] {
#    puts "ERROR: Cannot find executable $SURELOG_VERSION!"
#    exit 1
#}

set REGRESSION_PATH [pwd]

set SURELOG_COMMAND "$TIME $DEBUG_TOOL $SURELOG_VERSION"

set WINDOWS_BLACK_LIST [dict create]
dict set WINDOWS_BLACK_LIST Ariane 1
dict set WINDOWS_BLACK_LIST BlackParrot 1
dict set WINDOWS_BLACK_LIST BlackParrot2 1
dict set WINDOWS_BLACK_LIST CoresSweRV 1
dict set WINDOWS_BLACK_LIST SimpleIncludeAndMacros 1
dict set WINDOWS_BLACK_LIST TestFileSplit 1
dict set WINDOWS_BLACK_LIST UnitElabExternNested 1
dict set WINDOWS_BLACK_LIST UnitPython 1
dict set WINDOWS_BLACK_LIST UnitSimpleIncludeAndMacros 1
dict set WINDOWS_BLACK_LIST Verilator 1
dict set WINDOWS_BLACK_LIST BuildUVMPkg 1
dict set WINDOWS_BLACK_LIST Compl1001 1
dict set WINDOWS_BLACK_LIST YosysOpenSparc 1
dict set WINDOWS_BLACK_LIST Earlgrey_Verilator_0_1 1
dict set WINDOWS_BLACK_LIST Earlgrey_Verilator_01_05_21 1
dict set WINDOWS_BLACK_LIST Earlgrey_nexysvideo 1

set UNIX_BLACK_LIST [dict create]
# 2 message diff:
dict set UNIX_BLACK_LIST UnitElabExternNested 1

if { $tcl_platform(platform) == "windows" } {
    set BLACK_LIST $WINDOWS_BLACK_LIST
} else {
    set BLACK_LIST $UNIX_BLACK_LIST
}

proc findFiles { basedir pattern } {

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
        set subDirList [findFiles $dirName $pattern]
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
    set dirs "../tests/ ../third_party/tests/"
    set fileLists ""
    foreach dir $dirs {
        append fileList "[findFiles $dir *.sl] "
    }
    set testcommand ""
    set LONGESTTESTNAME 1
    set totaltest 0
    foreach file $fileList {
        regexp {([a-zA-Z0-9_/:-]+)/([a-zA-Z0-9_-]+)\.sl} $file tmp testdir testname
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

        set fid [open $testdir/$testname.sl]
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

proc run_regression { } {
    global TESTS TESTS_DIR SURELOG_COMMAND UHDM_DUMP_COMMAND LONGESTTESTNAME TESTTARGET ONETEST UPDATE USER ELAPSED PRIOR_USER PRIOR_ELAPSED MUTE TIME
    global DIFF_TESTS PRIOR_MAX_MEM MAX_MEM MAX_TIME PRIOR_MAX_TIME SHOW_DETAILS MT_MAX MP_MAX REGRESSION_PATH LARGE_TESTS LONG_TESTS DIFF_MODE SHELL SHELL_ARGS
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
    log [format "| %-*s | %-*s | %-*s | %-*s | %-*s | %-*s | %-*s | %-*s | %-*s |" $w1 "TESTNAME" $w2 "STATUS" $w6 "FATAL"  $w2 "SYNTAX" $w4 "ERROR" $w2 "WARNING"  $w7 "NOTE-UHDM"  $w5 "TIME" $w5 "MEM(Mb)"]
    log $sep

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
                log "$command [lindex $SURELOG_COMMAND 1]\n"
            } else {
                log "$SURELOG_COMMAND $command\n"
            }
        }

        if {$UPDATE == 1} {
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

        log_nonewline [format "| %-*s |" $w1 $testname]

        cd $testdir
        if {$DIFF_MODE == 0} {
            catch {file delete -force slpp_all slpp_unit} dummy
            catch {file delete -force $REGRESSION_PATH/tests/$test/slpp_all  $REGRESSION_PATH/tests/$test/slpp_unit} dummy
        }
        set passstatus "PASS"
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
                catch {set time_result [exec $SHELL $SHELL_ARGS "$TIME $command [lindex $SURELOG_COMMAND 1] > $REGRESSION_PATH/tests/$test/${testname}.log"]} time_result
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
                set command "$command -mt $MT_MAX -mp $MP_MAX $output_path"

                if {($ONETEST != "") && ($testname != $ONETEST)} {
                    continue
                }
                catch {set time_result [exec $SHELL $SHELL_ARGS "$SURELOG_COMMAND $command > $REGRESSION_PATH/tests/$test/${testname}.log"]} time_result
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
		catch {file delete -force slpp_all slpp_unit} dummy
                catch {file delete -force $REGRESSION_PATH/tests/$test/slpp_all  $REGRESSION_PATH/tests/$test/slpp_unit} dummy
                if [regexp {\.sh} $command] {
                    catch {set time_result [exec $SHELL $SHELL_ARGS "$TIME $command [lindex $SURELOG_COMMAND 1] > $REGRESSION_PATH/tests/$test/${testname}.log"]} time_result
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
            if {$DIFF_MODE == 1} {
                set SPEED [format "%-*s " 4 "${prior_elapsed}s"]
                set FASTER_OR_SLOWER 1
            } elseif [expr ($elapsed > $prior_elapsed) && ($no_previous_time_content == 0)] {
                set SPEED [format "%-*s %-*s " 3 "${elapsed}s" 3 "+[expr $elapsed - $prior_elapsed]"]
                set FASTER_OR_SLOWER 1
            } elseif [expr ($elapsed == $prior_elapsed) || ($no_previous_time_content)] {
                set SPEED [format "%-*s " 4 "${elapsed}s"]
            } else {
                set SPEED [format "%-*s %-*s " 3 "${elapsed}s" 3 "-[expr $prior_elapsed - $elapsed]"]
                set FASTER_OR_SLOWER 1
            }

            set prior_mem 0
            regexp {([0-9]+)maxresident} $time_content tmp prior_mem
            set prior_mem [expr $prior_mem / 1024]
            if {$PRIOR_MAX_MEM < $prior_mem} {
                set PRIOR_MAX_MEM $prior_mem
            }
            if {$DIFF_MODE == 1} {
                set MEM [format "%-*s " 4 "${prior_mem}"]
            } elseif [expr ($mem > $prior_mem) && ($no_previous_time_content == 0)] {
                set MEM  [format "%-*s %-*s " 3 "${mem}" 3 "+[expr $mem - $prior_mem]"]
                set DIFF_MEM 1
            } elseif  [expr ($mem == $prior_mem) || ($no_previous_time_content)] {
                set MEM [format "%-*s " 4 "${mem}"]
            } else {
                set MEM  [format "%-*s %-*s " 3 "${mem}" 3 "-[expr $prior_mem - $mem]"]
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

        log [format " %-*s | %-*s | %-*s | %-*s | %-*s | %-*s | %-*s | %-*s |" $w2 $passstatus $w6 $fatals $w2 $syntax $w4 $errors $w2 $warnings $w7 $notes $w5 $SPEED $w5 $MEM ]
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
            file delete -force slpp_all slpp_unit
            file delete -force $REGRESSION_PATH/tests/$test/slpp_all  $REGRESSION_PATH/tests/$test/slpp_unit
        }
	
        cd $REGRESSION_PATH/tests
    }
    log $sep
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
        puts $dummy
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
    if {$MUTE == 0} {
        exit 1
    } else {
        puts $LOG_CONTENT
    }
}

exit 0
