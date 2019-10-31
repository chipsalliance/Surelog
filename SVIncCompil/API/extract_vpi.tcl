#!/usr/bin/tclsh

set fid [open "vpi_user.h"]
set content [read $fid]
close $fid
set lines [split $content "\n"]

set ofid [open "enum.out" "w"]

foreach line $lines {
    if [regexp {(vpi[a-zA-Z0-9]+)} $line tmp vpiName] {
	regsub {vpi} $vpiName "sl" vpiName
	if ![info exist NAMES($vpiName)] {
	    set NAMES($vpiName) $vpiName
	    puts $ofid "      $vpiName,"
	}
    }
}
close $ofid
unset NAMES

set ofid [open "switch.out" "w"]

foreach line $lines {
    if [regexp {(vpi[a-zA-Z0-9]+)} $line tmp vpiName] {
	regsub {vpi} $vpiName "sl" vpiName
	if ![info exist NAMES($vpiName)] {
	    set NAMES($vpiName) $vpiName
	    puts $ofid "    case $vpiName:"
	    puts $ofid "      text = \"$vpiName\";"
	    puts $ofid "      break;"
	}
    }
}

close $ofid
