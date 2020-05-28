#!/usr/bin/tclsh

# Copyright 2020 Alain Dargelas
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

set mem [exec sh -c "free -m"]
set cpu [exec lscpu]
puts "MEMORY ON HOST:\n$mem"
puts "CPUs on HOST:\n$cpu"

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
    global TESTS TESTS_DIR  
    set dirs "../../tests/ ../../third_party/tests/"
    set fileLists ""
    foreach dir $dirs {
	append fileList "[findFiles $dir *.sl] "
    }
    set testcommand ""
    set LONGESTTESTNAME 1
    set totaltest 0
    foreach file $fileList {
	regexp {([a-zA-Z0-9_/-]+)/([a-zA-Z0-9_-]+)\.sl} $file tmp testdir testname
	regsub [pwd]/ $testdir "" testdir
	incr totaltest

	set fid [open $testdir/$testname.sl]
	set testcommand [read $fid]
	close $fid

	set TESTS($testname) $testcommand
	set TESTS_DIR($testname) $testdir
    }
}

proc run_regression { } {
    global TESTS
    set fid [open "CMakeLists.txt" "w"]
    puts $fid "cmake_minimum_required (VERSION 3.0)"
    puts $fid "project(SurelogRegression)"
    foreach testname [array names TESTS] {
	puts $fid "add_custom_command(OUTPUT $testname"
	puts $fid "  COMMAND ../tests/regression.tcl path=[file dirname [pwd]]/bin mute test=$testname"
	puts $fid "  WORKING_DIRECTORY ../"
	puts $fid ")"
    }

    puts $fid "add_custom_target(Regression ALL DEPENDS"
    foreach testname [array names TESTS] {
	puts $fid "  $testname"
    }
    puts $fid ")"

    close $fid
}

load_tests
run_regression

