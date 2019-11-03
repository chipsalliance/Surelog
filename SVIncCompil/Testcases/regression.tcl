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
  puts "               build=<debug, advanced, release, notcmalloc, undertow>"
  puts "               commit=\"commit text\""
  puts "               mt=<nbThreads>"
  puts "               large                             (large tests too)"
  puts "               show_diff                         (Shows text diff)"
  puts "regression.tcl update (Updates the diffs)"  
}


proc log { text } {
    global LOG_FILE
    puts $text
    flush stdout
    if ![info exist LOG_FILE] {
	set LOG_FILE [open regression.log "w"]
    }
    puts $LOG_FILE $text
    flush $LOG_FILE
}

proc log_nonewline { text } {
    global LOG_FILE
    puts -nonewline $text
    flush stdout
    if ![info exist LOG_FILE] {
	set LOG_FILE [open regression.log "w"]
    }
    puts -nonewline $LOG_FILE $text
    flush $LOG_FILE
}

set UPDATE 0
set TIME "/usr/bin/time" 
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
set LARGE_TESTS 0
set SHOW_DIFF 0
set LONG_TESTS(YosysOpenSparc) 1
set LONG_TESTS(YosysOldTests) 1
set LONG_TESTS(YosysRiscv) 1
set LONG_TESTS(YosysBigSim) 1
set LONG_TESTS(YosysBoom) 1
set LONG_TESTS(YosysEth) 1
set LONG_TESTS(YosysIce40) 1
set LONG_TESTS(YosysBigSimEllip) 1
set LONG_TESTS(YosysTests) 1
set LONG_TESTS(YosysBigSimBch) 1

if [regexp {show_diff}  $argv] {
    regsub "show_diff" $argv "" argv
    set SHOW_DIFF 1
}

if [regexp {large}  $argv] {
    set LARGE_TESTS 1
    log "Running large tests"
} else {
    log "Skipping large tests"
}

if [regexp {mt=([0-9]+)} $argv tmp MT_MAX] {
    log "Run with -mt $MT_MAX"
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

set TESTTARGET ""
set ONETEST ""
if [regexp {tests=([A-Za-z0-9_]+)} $argv tmp TESTTARGET] {
}
if [regexp {test=([A-Za-z0-9_]+)} $argv tmp TESTTARGET] {
    set ONETEST $TESTTARGET
}

set BUILD "release"
if [regexp {build=([A-Za-z0-9_]+)} $argv tmp BUILD] {
}

set SHOW_DETAILS 0
if [regexp {\-details} $argv] {
    set SHOW_DETAILS 1
}

if [regexp {update} $argv] {
    set UPDATE 1
}

log $argv

set COMMIT_TEXT ""
if [regexp {commit=([A-Za-z0-9_ \.]+)} $argv tmp COMMIT_TEXT] {
}

set SURELOG_VERSION "[pwd]/../dist/surelog/surelog"
set REGRESSION_PATH [pwd]

set SURELOG_COMMAND "$TIME $DEBUG_TOOL $SURELOG_VERSION"

proc init_regression { } {
    global BUILD 
    log "Creating release for regression..."
    cd ..
    log [exec sh -c "./release.tcl \"$BUILD tcmalloc\""]
    cd Testcases
}

proc load_tests { } {
    global TESTS TESTS_DIR LONGESTTESTNAME TESTTARGET ONETEST LARGE_TESTS LONG_TESTS
    set fid [open "../nbproject/launcher.properties"]
    set content [read $fid]
    close $fid
    set lines [split $content "\n"]
    set testcommand ""
    set LONGESTTESTNAME 1
    set totaltest 0
    foreach line $lines {
	if [regexp {launcher[0-9]+\.displayName=([a-zA-Z_0-9]+)} $line tmp testname] {
            set testcommand ""
	} elseif [regexp {launcher[0-9]+\.runCommand=\"\${PROJECT_DIR}/\${OUTPUT_PATH}\" (.*)} $line tmp testcommand] {    
	} elseif [regexp {launcher[0-9]+\.runCommand=(.*) \"\${PROJECT_DIR}/\${OUTPUT_PATH}\"} $line tmp testcommand] {    
	} elseif [regexp {launcher[0-9]+\.runDir=([a-zA-Z_0-9/-]+)} $line tmp testdir] {
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
	    
	    if {$LONGESTTESTNAME < [string length $testname]} {
		set LONGESTTESTNAME [string length $testname]
	    }
	    set TESTS($testname) $testcommand
	    set TESTS_DIR($testname) $testdir
	} else {
	    set testcommand "$testcommand $line"
	}	    
    }
    log "THERE ARE $totaltest tests"
    log "RUNNING   [array size TESTS] tests"
    log ""
}


proc count_messages { result } {
    set fatals -1
    set errors -1
    set warnings -1
    set notes -1
    set syntax 0
    # Normal test
    regexp {FATAL\] : ([0-9]+)} $result tmp fatals
    regexp {ERROR\] : ([0-9]+)} $result tmp errors
    regexp {WARNING\] : ([0-9]+)} $result tmp warnings
    regexp {NOTE\] : ([0-9]+)} $result tmp notes
    # Diff test
    if [regexp {\| FATAL \|[ ]*([0-9]+)[ ]*\|[ ]*([0-9]+)[ ]*} $result tmp fatal1 fatal2] {
	set fatals [expr $fatal1 + $fatal2]
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
	set errors 0
	set warnings 0
	set notes 0 
    }
    # stats per message ID

    set lines [split $result "\n"]
    foreach line $lines {
      	if [regexp {Syntax error} $line] {
	    incr syntax
	}
	if [regexp {(\[.*\])} $line tmp code] {
	    if [info exist CODES($code)] {
		incr CODES($code)
	    } else {
		set CODES($code) 1
	    }
	}
    }   
    set details ""
    foreach name [lsort -dictionary [array names CODES]] {
	lappend details [list $name $CODES($name)]
    }
    
    return [list $fatals $errors $warnings $notes $details $syntax]
}

proc run_regression { } {
    global TESTS TESTS_DIR SURELOG_COMMAND LONGESTTESTNAME TESTTARGET ONETEST UPDATE USER ELAPSED PRIOR_USER PRIOR_ELAPSED
    global DIFF_TESTS PRIOR_MAX_MEM MAX_MEM MAX_TIME PRIOR_MAX_TIME SHOW_DETAILS MT_MAX REGRESSION_PATH LARGE_TESTS LONG_TESTS
    set overrallpass "PASS"

    set w1 $LONGESTTESTNAME
    set w2 8
    set w4 8
    set w3 18
    set w5 12
    set MEM 0
    set sep +-[string repeat - $w1]-+-[string repeat - $w2]-+-[string repeat - $w2]-+-[string repeat - $w4]-+-[string repeat - $w2]-+-[string repeat - $w4]-+-[string repeat - $w2]-+-[string repeat - $w5]-+-[string repeat - $w5]-+
    log $sep
    log [format "| %-*s | %-*s | %-*s | %-*s | %-*s | %-*s | %-*s | %-*s | %-*s |" $w1 "TESTNAME" $w2 "STATUS"  $w2 "FATALS" $w4 "ERRORS" $w2 "WARNINGS"  $w4 "NOTES"  $w2 "SYNTAX"  $w5 "ELAPSED TIME" $w5 "MEM(Mb)"]
    log $sep
   
    foreach testname [array names TESTS] {	
	if {($ONETEST != "") && ($testname != $ONETEST)} {
	    continue
	}

	if {($ONETEST == "") && ($LARGE_TESTS == 0)} {
	    if [info exist LONG_TESTS($testname)] {
		continue
	    }
	}
	
	set testdir $TESTS_DIR($testname)
	regsub "Testcases/" $testdir "" test
	set command $TESTS($testname)
	regsub -all {\\} $command "" command
	if {($ONETEST != "")} {
	    log "\ncd $test"
	    if [regexp {\.sh} $command] {
		log "$command [lindex $SURELOG_COMMAND 1]\n"
	    } else {
		log "$SURELOG_COMMAND $command\n"
	    }
	}

	if {$UPDATE == 1} {
	    if [file exist "$test/${testname}_diff.log"] {
		log  [format "| %-*s | Copying $test/${testname}_diff.log to $test/${testname}.log" $w1 $testname]
		file copy -force "$test/${testname}_diff.log" "$test/${testname}.log"
		continue
	    } else {
		log  [format "| %-*s | No action" $w1 $testname]
		continue
	    }
	}
	
	log_nonewline [format "| %-*s |" $w1 $testname]

	cd $test
       	exec sh -c "rm -rf slpp*"
	
	set passstatus "PASS"
	if {($ONETEST != "") && [regexp {ddd} $SURELOG_COMMAND]} {
	    log "\nrun $command\n"
	    catch {set result [exec sh -c "$SURELOG_COMMAND"]} result
	    exit
	}
	if [regexp {\.sh} $command] {
	    catch {set result [exec sh -c "time $command [lindex $SURELOG_COMMAND 1]"]} result
	} else {
	    if {$MT_MAX != 0} {
		set command "$command -mt $MT_MAX"
	    }
	    catch {set result [exec sh -c "$SURELOG_COMMAND $command"]} result
	}
	set segfault 0
        if [regexp {Segmentation fault} $result] {
	    set segfault 1
	    exec sh -c "rm -rf slpp*"
	    if [regexp {\.sh} $command] {
		catch {set result [exec sh -c "time $command [lindex $SURELOG_COMMAND 1]"]} result
	    } else {
		catch {set result [exec sh -c "$SURELOG_COMMAND $command"]} result
	    }	    
	    if [regexp {Segmentation fault} $result] {
   	        set passstatus "FAIL"
                set overrallpass "FAIL"
		set segfault 2
	    } else {
		set segfault 0
	    }
        }
	if [regexp {AdvancedDebug} $SURELOG_COMMAND] {
	    log $result
	}

	set fatals -1
	set errors -1
	set warnings -1
	set notes -1

	set log_fatals -1
	set log_errors -1
	set log_warnings -1
	set log_notes -1
	set user 0
	set elapsed_min 0
	set elapsed 0
	set cpu 0
	foreach {fatals errors warnings notes details syntax} [count_messages $result] {}
	if [regexp {([0-9\.:]+)user [0-9\.:]+system ([0-9]+):([0-9\.]+)elapsed ([0-9]+)%CPU} $result tmp user elapsed_min elapsed cpu] {
	    set user [expr int($user)]
	    set elapsed [expr int(($elapsed_min *60) + $elapsed)]
	    set USER    [expr $USER + $user]
	    set ELAPSED [expr $ELAPSED + $elapsed]
	    if {$MAX_TIME < $elapsed} {
		set MAX_TIME $elapsed
	    }
	}
	set mem 0
	if [regexp {([0-9]+)maxresident} $result tmp mem] {
	    set mem [expr $mem / 1024]
	    if {$MAX_MEM < $mem} {
		set MAX_MEM $mem
	    }
	}
	
	set SPEED ""
	set FASTER_OR_SLOWER 0
	set DIFF_MEM 0
	if [file exists "$testname.log"] {
	    set fid [open "$testname.log" "r"]
	    set content [read $fid]
	    close $fid
	    foreach {log_fatals log_errors log_warnings log_notes log_details log_syntax} [count_messages $content] {}
	    set prior_user 0
	    set prior_elapsed_min 0
	    set prior_elapsed 0
	    set cpu 0
	    if [regexp {([0-9\.]+)user [0-9\.:]+system ([0-9]+):([0-9\.]+)elapsed ([0-9]+)%CPU} $content tmp prior_user prior_elapsed_min prior_elapsed cpu] {
		set prior_user [expr int($prior_user)]
		set prior_elapsed [expr int(($prior_elapsed_min *60) + $prior_elapsed)]
		set PRIOR_USER    [expr $PRIOR_USER + $prior_user]
		set PRIOR_ELAPSED [expr $PRIOR_ELAPSED +  $prior_elapsed]
		if {$PRIOR_MAX_TIME < $prior_elapsed} {
		    set PRIOR_MAX_TIME $prior_elapsed
		}
		if [expr $elapsed > $prior_elapsed] {
		    set SPEED [format "%-*s %-*s " 4 "${elapsed}s" 5 "(+[expr $elapsed - $prior_elapsed]s)"]
		    set FASTER_OR_SLOWER 1
		} elseif [expr $elapsed == $prior_elapsed] {
		    set SPEED [format "%-*s " 4 "${elapsed}s"]
		} else {
		    set SPEED [format "%-*s %-*s " 4 "${elapsed}s" 5 "(-[expr $prior_elapsed - $elapsed]s)"]
		    set FASTER_OR_SLOWER 1
		}
	    }

	    set prior_mem 0
	    if [regexp {([0-9]+)maxresident} $content tmp prior_mem] {
		set prior_mem [expr $prior_mem / 1024]
		if {$PRIOR_MAX_MEM < $prior_mem} {
		    set PRIOR_MAX_MEM $prior_mem
		}
		if [expr $mem > $prior_mem] {
		    set MEM  [format "%-*s %-*s " 4 "${mem}" 5 "(+[expr $mem - $prior_mem])"]
		    set DIFF_MEM 1
		} elseif  [expr $mem == $prior_mem] {
		    set MEM [format "%-*s " 4 "${mem}"]
		} else {
		    set MEM  [format "%-*s %-*s " 4 "${mem}" 5 "(-[expr $prior_mem - $mem])"]
		    set DIFF_MEM 1
		}
		
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
	    set fatals "segfault"
	    set passstatus "FAIL"
            set overrallpass "FAIL"
	}
	if {$segfault == 1 || $segfault == 2} {
	    set fatals "segfault"
	}
	
	log [format " %-*s | %-*s | %-*s | %-*s | %-*s | %-*s | %-*s | %-*s |" $w2 $passstatus $w2 $fatals $w4 $errors $w2 $warnings $w4 $notes $w2 $syntax $w5 $SPEED $w5 $MEM ]
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
	if {(($passstatus == "PASS") && ($DIFF_MEM == 0) && ($FASTER_OR_SLOWER == 0)) || ($UPDATE == 1)} {
	    set fid [open "$testname.log" "w"]
	} else {
	    set fid [open "${testname}_diff.log" "w"]
	}
	puts $fid $result
	close $fid
	
	cd $REGRESSION_PATH
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

init_regression
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

foreach testname [array names DIFF_TESTS] {
    if {$SHOW_DIFF == 0} {
	log " tkdiff $DIFF_TESTS($testname)/${testname}.log $DIFF_TESTS($testname)/${testname}_diff.log"
    } else {
	log "diff $DIFF_TESTS($testname)/${testname}.log $DIFF_TESTS($testname)/${testname}_diff.log"
	catch {exec sh -c "diff -y $DIFF_TESTS($testname)/${testname}.log $DIFF_TESTS($testname)/${testname}_diff.log"} dummy
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
