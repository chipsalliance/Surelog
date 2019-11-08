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

# Either creates all releases, or just the one passed as argument:
#
# ./release.tcl
#
# Or
#
# ./release.tcl "<build_type> <lib_type>"
#
# Ex.: ./release.tcl  "release  tcmalloc"

#  build_type: release, debug, advanced (debug)

#set RELEASES { { "release"  "notcmalloc" }  { "release"  "tcmalloc" } \
#               { "debug"    "notcmalloc" }  { "debug"    "tcmalloc" } \
#	       { "advanced" "notcmalloc" }  { "advanced" "tcmalloc" } \
#             } 

set RELEASES { { "release"  "notcmalloc" }  { "release"  "tcmalloc" } \
               { "debug"    "notcmalloc" }  { "debug"    "tcmalloc" } 
             } 


if {$argv != ""} {
    set RELEASES $argv
} 

proc precompilePackages { } {
    set source_file "../parser/SV3_1aParser.cpp"
    set compiled_file "Release/GNU-Linux/pkg/work/uvm_pkg.sv.slpa"
    set source_time 0
    if [file exist $source_file] {
	set source_time [file mtime $source_file]
    }
    set compiled_time 0
    if [file exist $compiled_file] {
	set compiled_time [file mtime $compiled_file]
    }
    exec sh -c "rm -rf Release/sv"
    exec sh -c "mkdir -p Release/sv; cp ../API/builtin.sv Release/sv"
    if {($compiled_time == 0) || ($source_time >= $compiled_time)} {
	exec sh -c "rm -rf slpp_all"
	exec sh -c "rm -rf slpp_unit"
	exec sh -c "rm -rf dist/slpp_all"
	exec sh -c "rm -rf dist/slpp_unit"
	exec sh -c "rm -rf Release/GNU-Linux/pkg/work/"
	exec sh -c "rm -f ovm-2.1.2 uvm-1.2 vmm-1.1.1a"
	exec sh -c "ln -s ../../UVM/ovm-2.1.2 ovm-2.1.2"
	exec sh -c "ln -s ../../UVM/uvm-1.2 uvm-1.2"
	exec sh -c "ln -s ../../UVM/vmm-1.1.1a vmm-1.1.1a"
	puts "Precompiling ovm_pkg..."
	puts "Begin: The time is: [clock format [clock seconds] -format %H:%M:%S]"
	exec sh -c "Release/GNU-Linux/surelog -profile -createcache +incdir+ovm-2.1.2/src/ +incdir+vmm-1.1.1a/sv ovm-2.1.2/src/ovm_pkg.sv -writepp -verbose  -mt 0 -parse; cp slpp_all/surelog.log ovm_pkg.log" 
	puts "End: The time is: [clock format [clock seconds] -format %H:%M:%S]"
	puts "Precompiling uvm_pkg..."
	puts "Begin: The time is: [clock format [clock seconds] -format %H:%M:%S]"
	exec sh -c "Release/GNU-Linux/surelog -profile -createcache +incdir+.+uvm-1.2/src/ uvm-1.2/src/uvm_pkg.sv -writepp -verbose  -mt 0 -parse; cp slpp_all/surelog.log uvm_pkg.log" 
	puts "End: The time is: [clock format [clock seconds] -format %H:%M:%S]"
	
    } else {
	puts "Skipping ovm_pkg..."
	puts "Skipping uvm_pkg..."

    }
    
    catch {exec sh -c "cp -R -f Release/GNU-Linux/pkg/work Debug/GNU-Linux/pkg"} dummy
    catch {exec sh -c "cp -R -f Release/GNU-Linux/pkg/work AdvancedDebug/GNU-Linux/pkg"} dummy 
    catch {exec sh -c "cp -R -f Release/GNU-Linux/pkg/work ReleaseNoTcMalloc/GNU-Linux/pkg"} dummy 

}

proc createReleases { } {
    global RELEASES 
    foreach release $RELEASES {
	set build_type [lindex $release 0] 
	set lib_type   [lindex $release 1] 
	set tar_filename "surelog_${build_type}_${lib_type}"
	catch {exec sh -c "chmod 777 -R surelog/"} dummy
	exec sh -c "rm -rf surelog"
	file mkdir surelog
	file mkdir surelog/bin
	file mkdir surelog/bin/pkg
	file mkdir surelog/bin/pkg/work
	file mkdir surelog/lib
	file mkdir surelog/python
	file mkdir surelog/sv
	file copy  Release/GNU-Linux/pkg/work/uvm_pkg.sv.slpp surelog/bin/pkg/work
	file copy  Release/GNU-Linux/pkg/work/uvm_pkg.sv.slpa surelog/bin/pkg/work
	file copy  Release/GNU-Linux/pkg/work/ovm_pkg.sv.slpp surelog/bin/pkg/work
	file copy  Release/GNU-Linux/pkg/work/ovm_pkg.sv.slpa surelog/bin/pkg/work
	if {($build_type == "release")} {
	    if {$lib_type == "tcmalloc"} {
		file copy Release/GNU-Linux/surelog surelog/bin/surelog.exe
		catch {exec sh -c "mkdir -p Release/python; ln -s ../../../API/slSV3_1aPythonListener.py Release/python"} dummy
		catch {exec sh -c "mkdir -p Release/sv; ln -s ../../../API/builtin.sv Release/sv"} dummy
	    } else {
		file copy ReleaseNoTcMalloc/GNU-Linux/surelog surelog/bin/surelog.exe
		catch {exec sh -c "mkdir -p ReleaseNoTcMalloc/python; ln -s ../../../API/slSV3_1aPythonListener.py ReleaseNoTcMalloc/python"} dummy
		catch {exec sh -c "mkdir -p ReleaseNoTcMalloc/sv; ln -s ../../../API/builtin.sv ReleaseNoTcMalloc/sv"} dummy
	    }
	} elseif {$build_type == "debug"}  {
	    file copy Debug/GNU-Linux/surelog surelog/bin/surelog.exe
	    catch {exec sh -c "mkdir -p Debug/python; ln -s ../../../API/slSV3_1aPythonListener.py Debug/python"} dummy
	    catch {exec sh -c "mkdir -p Debug/sv; ln -s ../../../API/builtin.sv Debug/sv"} dummy
	} elseif {$build_type == "advanced"}  {
	    file copy AdvancedDebug/GNU-Linux/surelog surelog/bin/surelog.exe
	    catch {exec sh -c "mkdir -p AdvancedDebug/python; ln -s ../../../API/slSV3_1aPythonListener.py AdvancedDebug/python"} dummy
	    catch {exec sh -c "mkdir -p AdvancedDebug/sv; ln -s ../../../API/builtin.sv AdvancedDebug/sv"} dummy
	} else {
	    puts "ERROR!!! UNSUPPORTED BUILD TYPE: $build_type"
	    exit
	}

	if {$lib_type == "tcmalloc"} {
	    catch {file copy /usr/lib/x86_64-linux-gnu/libtcmalloc.so.4 surelog/lib/} dummy
	    catch {file copy /usr/lib/x86_64-linux-gnu/libtcmalloc.so.4.2.6 surelog/lib/} dummy
	    catch {file copy /usr/lib/libtcmalloc.so.4 surelog/lib/} dummy
	    catch {file copy /usr/lib/libtcmalloc.so.4.2.6 surelog/lib/} dummy
	    #if ![file exists "surelog/lib/libtcmalloc.so.4"] {
	   #	error "No Tclmalloc found on system"
	   # }

	}

	file copy ../API/slSV3_1aPythonListener.py surelog/python/
	file copy ../API/slformatmsg.py surelog/python/slformatmsg.py
	file copy ../API/slwaivers.py surelog/python/
	file copy ../API/surelog.bash surelog/surelog
	file copy ../API/yosys.tcl surelog/yosys.tcl
	file copy ../API/builtin.sv surelog/sv
	catch {set copy_result [file copy /usr/local/lib64/libstdc++.so.6.0.21 surelog/lib/libstdc++.so.6]} copy_result
	catch {set copy_result [file copy /usr/local/lib64/libgcc_s.so.1 surelog/lib/]} copy_result
	exec sh -c "chmod 555 -R surelog/"
	
	exec sh -c "tar cvzf ${tar_filename}.tar.gz surelog/"
	puts "Created  dist/${tar_filename}.tar.gz"
    }

}

proc testReleases { } {
    global RELEASES 
    foreach release $RELEASES {
	set build_type [lindex $release 0] 
	set lib_type   [lindex $release 1] 
	set tar_filename "surelog_${build_type}_${lib_type}"

	exec sh -c "chmod 777 -R surelog/"
	exec sh -c "rm -rf surelog"

	exec sh -c "tar xvzf ${tar_filename}.tar.gz"

	catch {exec sh -c "chmod 777 -R surelog_test/"} dummy
	exec sh -c "rm -rf surelog_test"
	file mkdir surelog_test
	file copy "../python_listener.py" "surelog_test/slSV3_1aPythonListener.py"
	cd surelog_test
	
	set fid [open "test.v" "w"]
	puts $fid "module toto();\
                   `TOTO  \
                   endmodule"
	close $fid

	catch {set result [exec sh -c "../surelog/surelog test.v -parse -pythonlistener"]} result
	if {[regexp {PY0403} $result] && [regexp {module toto} $result]} {
	    puts "PASS: $tar_filename"
	} else {
	    puts "FAIL: $tar_filename"
	    puts "$result"
	}

	cd ..

    }

}

cd dist

precompilePackages

createReleases 

testReleases 

cd ..


