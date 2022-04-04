#!/usr/bin/env tclsh

proc parse { file } {
    puts "Parsing $file"
    set fid [open $file]
    set content [read $fid]
    set lines [split $content "\n"]
    set fod [open "hierarchy.txt" "w"]
    foreach line $lines {
	if [regexp {(chip_earlgrey_verilator__DOT__[a-zA-Z0-9_]*)} $line tmp path] {
	    regsub -all {__DOT__} $path "." path 
	    regsub -all {__BRA__} $path "\[" path 
	    regsub -all {__KET__} $path "\]" path 
	    regsub {\.[a-zA-Z0-9_]*$} $path "" path
	    set PATHS($path) 1
	}
    }
    close $fid

    foreach path [lsort -dictionary [array names PATHS]] {
	puts $fod $path
    }
    close $fod
    puts "Wrote hierarchy in hierarchy.txt" 
}

parse $argv
