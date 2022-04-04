#!/usr/bin/env tclsh

proc parse { file gl } {
    global $gl
    puts "Parsing $file"
    set fid [open $file]
    set content [read $fid]
    set lines [split $content "\n"]
    foreach line $lines {
	set [subst $gl]($line) 1
    }
    close $fid
}

parse [lindex $argv 0] FROM
parse [lindex $argv 1] TO

foreach path [lsort -dictionary [array names FROM]] {
    if ![info exist TO($path)] {
	puts "Missing $path"
    }
}

