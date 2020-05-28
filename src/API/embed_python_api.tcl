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



set fid [open "API/slapi.py"]
set content [read $fid]
close $fid

set fid [open "API/slformatmsg.py"]
set content "$content\n[read $fid]"
close $fid

set lines [split $content "\n"]
set oid [open "API/slapi_scripts.h" "w"]

puts $oid "std::vector<std::string> slapi_scripts = {"   

puts $oid "\"import slapi\\n\""

set pack 0
foreach line $lines {
    if [regexp {^def SL} $line] {
	set pack 1
    }
    if {$pack == 1} {
	regsub -all {_slapi} $line "slapi" line
	regsub -all {\\n} $line "\\\\\\n" line
	regsub -all {\"} $line "\\\"" line
	puts $oid "\"$line\\n\""
    }
}

puts $oid "};"

flush $oid
close $oid

