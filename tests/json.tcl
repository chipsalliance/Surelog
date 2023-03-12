#
#   JSON parser for Tcl.
#
#   See http://www.json.org/ && http://www.ietf.org/rfc/rfc4627.txt
#
#   Copyright 2006 ActiveState Software Inc.
#
#   $Id: json.tcl,v 1.2 2006/08/25 23:19:53 hobbs Exp $
#

if {$::tcl_version < 8.5} {
    package require dict
}

package provide json 1.0

namespace eval json {}

proc json::getc {{txtvar txt}} {
    # pop single char off the front of the text
    upvar 1 $txtvar txt
    if {$txt eq ""} {
    	return -code error "unexpected end of text"
    }

    set c [string index $txt 0]
    set txt [string range $txt 1 end]
    return $c
}

proc json::json2dict {txt} {
    return [_json2dict]
}

proc json::_json2dict {{txtvar txt}} {
    upvar 1 $txtvar txt

    set state TOP

    set txt [string trimleft $txt]
    while {$txt ne ""} {
    	set c [string index $txt 0]

    	# skip whitespace
    	while {[string is space $c]} {
    	    getc
    	    set c [string index $txt 0]
    	}

	if {$c eq "\{"} {
	    # object
	    switch -- $state {
		TOP {
		    # we are dealing with an Object
		    getc
		    set state OBJECT
		    set dictVal [dict create]
		}
		VALUE {
		    # this object element's value is an Object
		    dict set dictVal $name [_json2dict]
		    set state COMMA
		}
		LIST {
		    # next element of list is an Object
		    lappend listVal [_json2dict]
		    set state COMMA
		}
		default {
		    return -code error "unexpected open brace in $state mode"
		}
	    }
	} elseif {$c eq "\}"} {
	    getc
	    if {$state ne "OBJECT" && $state ne "COMMA"} {
		return -code error "unexpected close brace in $state mode"
	    }
	    return $dictVal
	} elseif {$c eq ":"} {
	    # name separator
	    getc

	    if {$state eq "COLON"} {
		set state VALUE
	    } else {
		return -code error "unexpected colon in $state mode"
	    }
	} elseif {$c eq ","} {
	    # element separator
	    if {$state eq "COMMA"} {
		getc
		if {[info exists listVal]} {
		    set state LIST
		} elseif {[info exists dictVal]} {
		    set state OBJECT
		}
	    } else {
		return -code error "unexpected comma in $state mode"
	    }
	} elseif {$c eq "\""} {
	    # string
	    # capture quoted string with backslash sequences
	    set reStr {(?:(?:\")(?:[^\\\"]*(?:\\.[^\\\"]*)*)(?:\"))}
	    set string ""
	    if {![regexp $reStr $txt string]} {
		set txt [string replace $txt 32 end ...]
		return -code error "invalid formatted string in $txt"
	    }
	    set txt [string range $txt [string length $string] end]
	    # chop off outer ""s and substitute backslashes
	    # This does more than the RFC-specified backslash sequences,
	    # but it does cover them all
	    set string [subst -nocommand -novariable \
			    [string range $string 1 end-1]]

	    switch -- $state {
		TOP {
		    return $string
		}
		OBJECT {
		    set name $string
		    set state COLON
		}
		LIST {
		    lappend listVal $string
		    set state COMMA
		}
		VALUE {
		    dict set dictVal $name $string
		    unset name
		    set state COMMA
		}
	    }
	} elseif {$c eq "\["} {
	    # JSON array == Tcl list
	    switch -- $state {
		TOP {
		    getc
		    set state LIST
		}
		LIST {
		    lappend listVal [_json2dict]
		    set state COMMA
		}
		VALUE {
		    dict set dictVal $name [_json2dict]
		    set state COMMA
		}
		default {
		    return -code error "unexpected open bracket in $state mode"
		}
	    }
	} elseif {$c eq "\]"} {
	    # end of list
	    getc
	    if {![info exists listVal]} {
		#return -code error "unexpected close bracket in $state mode"
		# must be an empty list
		return ""
	    }

	    return $listVal
	} elseif {0 && $c eq "/"} {
	    # comment
	    # XXX: Not in RFC 4627
	    getc
	    set c [getc]
	    switch -- $c {
		/ {
		    # // comment form
		    set i [string first "\n" $txt]
		    if {$i == -1} {
			set txt ""
		    } else {
			set txt [string range $txt [incr i] end]
		    }
		}
		* {
		    # /* comment */ form
		    getc
		    set i [string first "*/" $txt]
		    if {$i == -1} {
			return -code error "incomplete /* comment"
		    } else {
			set txt [string range $txt [incr i] end]
		    }
		}
		default {
		    return -code error "unexpected slash in $state mode"
		}
	    }
	} elseif {[string match {[-0-9]} $c]} {
	    # one last check for a number, no leading zeros allowed,
	    # but it may be 0.xxx
	    string is double -failindex last $txt
	    if {$last > 0} {
		set num [string range $txt 0 [expr {$last - 1}]]
		set txt [string range $txt $last end]

		switch -- $state {
		    TOP {
			return $num
		    }
		    LIST {
			lappend listVal $num
			set state COMMA
		    }
		    VALUE {
			dict set dictVal $name $num
			set state COMMA
		    }
		    default {
			getc
			return -code error "unexpected number '$c' in $state mode"
		    }
		}
	    } else {
		getc
		return -code error "unexpected '$c' in $state mode"
	    }
	} elseif {[string match {[ftn]} $c]
		  && [regexp {^(true|false|null)} $txt val]} {
	    # bare word value: true | false | null
	    set txt [string range $txt [string length $val] end]

	    switch -- $state {
		TOP {
		    return $val
		}
		LIST {
		    lappend listVal $val
		    set state COMMA
		}
		VALUE {
		    dict set dictVal $name $val
		    set state COMMA
		}
		default {
		    getc
		    return -code error "unexpected '$c' in $state mode"
		}
	    }
	} else {
	    # error, incorrect format or unexpected end of text
	    return -code error "unexpected '$c' in $state mode"
	}
    }
}

proc json::dict2json {dictVal} {
    # XXX: Currently this API isn't symmetrical, as to create proper
    # XXX: JSON text requires type knowledge of the input data
    set json ""

    dict for {key val} $dictVal {
	# key must always be a string, val may be a number, string or
	# bare word (true|false|null)
	if {0 && ![string is double -strict $val]
	    && ![regexp {^(?:true|false|null)$} $val]} {
	    set val "\"$val\""
	}
    	append json "\"$key\": $val," \n
    }

    return "\{${json}\}"
}

proc json::list2json {listVal} {
    return "\[$[join $listVal ,]\]"
}

proc json::string2json {str} {
    return "\"$str\""
}
