#!/usr/bin/tclsh

proc parse { file } {
    puts "Parsing $file"
    set fid [open $file]
    set content [read $fid]
    set lines [split $content "\n"]
    set fod [open "sorted.txt" "w"]
    foreach line $lines {
	regsub {work@} $line "" line
	set PATHS($line) 1
    }
    close $fid

    foreach path [lsort -dictionary [array names PATHS]] {
	puts $fod $path
    }
    close $fod
    puts "Wrote sorted hierarchy in sorted.txt" 
}

parse $argv
