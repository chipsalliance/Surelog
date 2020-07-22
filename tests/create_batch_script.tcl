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

# This script creates a batch script for Surelog.
# - It analyzes recursively the directories under the working directory and searches for .sv files by default
# - It takes an optionnal <command> line option to add a <command> invokation from Surelog.
#   Surelog will invoke that linux command with a filelist passed as argument.
# - The resulting batch file batch.txt can be passed to surelog

# Usages:
# create_batch_script.tcl [exe=<Linux executable>] [ext=<.v,.sv,...>] [batch=<script_name>] [options="<surelog options>"]
#                       
#
# Example:
# create_batch_script.tcl exe=verible ext=.v,.sv batch=batch.txt options="-writepp -parse"
#
# surelog -batch batch.txt
#
puts "Command line: $argv"

set EXTENSIONS      ".sv"
set EXECUTABLE      ""
set BATCH_SCRIPT    "batch.txt"
set SURELOG_OPTIONS "-writepp -parse -nocache -nobuiltin -noinfo -nocomp -noelab -timescale=1ns/1ns -nostdout"

if [regexp {exe=([a-zA-Z0-9_/\.]+)} $argv tmp EXECUTABLE] {
    puts "Creating callbacks to: $EXECUTABLE"
}

if [regexp {batch=([a-zA-Z0-9_/\.]+)} $argv tmp BATCH_SCRIPT] {
}

if [regexp {ext=([a-zA-Z0-9_/\.,]+)} $argv tmp EXTENSIONS] {
}

if [regexp {\{options=(.*)\}} $argv tmp SURELOG_OPTIONS] {
}


puts "Creating batch script: $BATCH_SCRIPT"

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


proc create_file_list {} {
    global EXTENSIONS EXECUTABLE BATCH_SCRIPT SURELOG_OPTIONS 

    set fid [open $BATCH_SCRIPT "w"]
    set fileList ""
    foreach EXT [split $EXTENSIONS ","] {
	puts "Scanning for *$EXT files"
	append fileList "[findFiles . *$EXT] "
    }
    regsub -all "[pwd]/" $fileList "" fileList
    set count 0
    foreach file $fileList {
	if [regexp "slpp" $file] {
	    continue
	}
	set cmd "-cd [file dirname $file] $SURELOG_OPTIONS [file tail $file] -l [file tail $file].log"
	
	if {$EXECUTABLE != ""} {
	    set cmd "$cmd -exe $EXECUTABLE"
	}
	puts $fid $cmd
	#puts $cmd
	incr count
    }
    close $fid
    puts "Created $count batch commands in: $BATCH_SCRIPT"
    puts "Please run surelog -batch $BATCH_SCRIPT"
}

create_file_list
