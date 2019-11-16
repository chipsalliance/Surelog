++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
## SURELOG project
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
### Executable: surelog
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

### Dependancies Install 

Please see [`INSTALL`](../INSTALL.md)

### Build
 cd Surelog
 make

### Run a test

* dist/Release/GNU-Linux/surelog -help
* dist/Release/GNU-Linux/surelog -writepp -parse tests/UnitTest/top.v

++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
## Modus operanti for grammar development:

* Edit the grammar file in the G4 directory, test the grammar locally with the java targets: 
  * cd Surelog/grammar; ant compile_java; ant javac; ant test_pp_tokens

++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
## TESTS and REGRESSIONS

The following regression script will run all tests under tests and third_party/tests:
* cd build
* ../tests/regression.tcl 

Regression options:
* regression.tcl help   
* regression.tcl tests=<testname>     (Tests matching regular expression)
  * test=<testname>                   (Just that test)
  * debug=<none, valgrind, ddd>
  * build=<debug, release>
  * mt=<nbThreads>                    (Number of threads per process -
                                       regression runs 1 process at a time)
  * large                             (large tests too)
  * show_diff                         (Shows text diff)
* regression.tcl update (Updates the diffs)  

++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
## RELEASES

* ./release.tcl Releases the following:

* ./release.tcl
   * Created  dist/surelog_release_tcmalloc.tar.gz

Run this script at least once to create symbolic links for the Python Listener

++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
## PROFILING

* Either
   * env CPUPROFILE=./prof env LD_PRELOAD="/usr/lib/libprofiler.so"  ../../dist/Debug/GNU-Linux/surelog <test>
* Or 
   * google-pprof --callgrind  ../../dist/Debug/GNU-Linux/surelog prof >> call
   * kcachegrind call 

* Get Google tools: 
   * sudo apt-get install google-perftools graphviz
   * sudo apt-get install libgoogle-perftools-dev
   * sudo apt-get install gperftools

++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
## SOURCE FORMATTING

clang-format -i -style=Google -sort-includes=false <files>

++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
## Useful links:

http://ecee.colorado.edu/~mathys/ecen2350/IntelSoftware/pdf/IEEE_Std1800-2017_8299595.pdf
https://google.github.io/flatbuffers/flatbuffers_guide_use_cpp.html
https://www.csee.umbc.edu/portal/help/VHDL/verilog/command_line_plus_options.html
http://sven.xtreme-eda.com/
https://www.edaplayground.com/

++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
