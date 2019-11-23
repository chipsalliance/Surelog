++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
## SURELOG project
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
### Executable: surelog
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

### Dependancies Install 

Please see [`INSTALL`](../INSTALL.md)

### Build
 * cd Surelog
```bash
make
make install (/usr/local/bin and /usr/local/lib/surelog by default, use DESTDIR= for alternative locations)
```

### Run a test

* When in the Surelog/build directory, run one of the following:

* dist/Release/surelog -help

* dist/Release/surelog -writepp -parse ../tests/UnitElabBlock/top.v

* dist/Release/hellosureworld ../tests/UnitElabBlock/top.v -parse -mutestdout

### Create your own executable with the libsurelog.a library

* The CMake file Surelog/tests/TestInstall/CMakeLists.txt contains the instructions to create your own executable that uses the surelog library for design parsing and creation of the Design/Testbench data model.

* The source file Surelog/src/hellosureworld.cpp contains the "HelloWorld" for surelog library usage and data model browsing. 

++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
## Modus operanti for grammar development:

* Edit the grammar file in the G4 directory, test the grammar locally with the java targets: 
  * cd Surelog/grammar;
  * ant compile_java;
  * ant javac;
  * ant test_pp_tokens or
  * ant test_tree ... (There are several debug targets in the build.xml)

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
## PROFILING

* Either
   * env CPUPROFILE=./prof env LD_PRELOAD="/usr/lib/libprofiler.so"  build/dist/Debug/surelog <test>
* Or 
   * google-pprof --callgrind  build/dist/Debug/surelog prof >> call
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
