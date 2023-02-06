#!/usr/bin/env tclsh

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
# - The "verification" option does not generate a batch, instead it creates one script per testcase, and calls the script .slv instead of .sl to be used by "regression.tcl verification"

# Usages:
# create_batch_script.tcl [exe=<Linux executable>] [ext=<.v,.sv,...>] [batch=<script_name>] [options="<surelog options>"] [verification]
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
set VERIFICATION 0

if [regexp {exe=([a-zA-Z0-9_/\.]+)} $argv tmp EXECUTABLE] {
    puts "Creating callbacks to: $EXECUTABLE"
}

if [regexp {batch=([a-zA-Z0-9_/\.]+)} $argv tmp BATCH_SCRIPT] {
}

if [regexp {ext=([a-zA-Z0-9_/\.,]+)} $argv tmp EXTENSIONS] {
}

if [regexp {\{options=(.*)\}} $argv tmp SURELOG_OPTIONS] {
}

if [regexp {verification} $argv] {
    set VERIFICATION 1
    regsub "verification" $argv "" argv
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
    global EXTENSIONS EXECUTABLE BATCH_SCRIPT SURELOG_OPTIONS VERIFICATION
    if {$VERIFICATION == 0} { 
        set fid [open $BATCH_SCRIPT "w"]
    }
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
	set fid1 [open $file]
	set content [read $fid1]
	close $fid1
	set dir_name [file dirname $file]
	set uvm_dir "../../../UVM/1800.2-2017-1.0/src/"
	if {$dir_name == "."} {
	    set uvm_dir "../../UVM/1800.2-2017-1.0/src/"
	} elseif [regexp {/} $dir_name] {
	    set uvm_dir "../../../../UVM/1800.2-2017-1.0/src/"
	}
	set import_uvm ""
	if [regexp {import[ ]+uvm_pkg} $content] {
	    set import_uvm "$uvm_dir/uvm_pkg.sv"
	}
        set cmd ""
        if {$VERIFICATION == 0} { 
            set cmd "-cd $dir_name"
        }
	append cmd " -I$uvm_dir $import_uvm $SURELOG_OPTIONS [file tail $file]"
        if {$VERIFICATION == 0} {
            append cmd " -l [file tail $file].log"
        }
	if {$EXECUTABLE != ""} {
	     append cmd " -exe $EXECUTABLE"
	}
        if {$VERIFICATION == 0} { 
            puts $fid $cmd
        } else {
            set file_name [file tail $file]
            set full_name "$dir_name/[file tail $dir_name]_${file_name}.slv"
            if {[regexp {_256_} $full_name] || [regexp {_128_} $full_name] || [regexp {_64_} $full_name]} {
                # Large designs from the bsg small design regression
                continue
            }
            set fid [open $full_name "w"]
            puts $fid $cmd
            close $fid
        }
	incr count
    }
    if {$VERIFICATION == 0} { 
        close $fid
    }
    puts "Created $count batch commands in: $BATCH_SCRIPT"
    puts "Please run surelog -batch $BATCH_SCRIPT"
}

create_file_list
