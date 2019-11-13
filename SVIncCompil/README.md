++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
## SURELOG project
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
### Executable: surelog
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

### Development Environment Required:

* Linux (Ubuntu or Centos)

* Unlimit all limits, in your .cshrc or .bashrc put "ulimit -s"
  that will enable gcc to compile the very large Antlr generated C++ files

* The following tools need to be installed on your machine:
  * Java jdk (For Antlr generation)
    sudo apt-get install default-jdk
  * Compiler: gcc with C11 support
    * gcc > 5.4
    Example of gcc (Used for Travis build):
       * sudo add-apt-repository ppa:jonathonf/gcc-7.2
       * sudo apt-get update
       * sudo apt-get install gcc-7 g++-7
  * Python3.6
  * uuid
  * uuid-dev
  * cmake
  * tclsh
  * maven
  * git
  * swig
  * pkg-config
  * Java "ant" build system (For G4 directory)
  * IDE: >= netbeans8.2
  * ddd for core dump debug
  * valgrind --tool=memcheck to check for memory corruptions
  * tcmalloc

* Surelog Source code
git clone https://github.com/alainmarcel/Surelog.git

### Build

* Run 3rd party build script (Builds antlr4.7.2, python3.6, flatbuffer, ccache)
   * cd Surelog/SVIncCompil
   * ./build3rdparty.sh

* Build Surelog
Pick your choice:
   * ./buildall.sh       (Builds all targets, release, debug...)
   * ./buildrelease.sh   (Builds the release target)
   * ./builddebug.sh     (Builds the debug target)
   * ./buildreleasepp.sh (Updates the preprrocessor grammar and build the release target)
   * ./buildpp.sh        (Updates the preprrocessor grammar and build all targets)


### Run a test

* dist/Release/GNU-Linux/surelog -help
* dist/Release/GNU-Linux/surelog -writepp -parse ../TESTCASES/UnitTest/top.v

++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
## Modus operanti for grammar development:

* Edit the grammar file in the G4 directory, test the grammar locally with the java targets: 
ant compile_java; ant javac; ant test_pp_tokens

* Then generate for the C++ target and copy the cpp files in SVIncCompil/parser: ant compile_cpp; ant copy_cpp

* Import the project SVIncCompil in NetBeans, develop using the imported antlr generated code.

Voila! 

++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
## TESTS and REGRESSIONS

Create tests in Netbeans under the Testcase directory,
 Copy an exisitng launcher in the Project Manager Launcher menu, adapt to the test

The following regression script will run all tests:
* cd Testcases
* ./regression.tcl

Regression options:
* regression.tcl help   
* regression.tcl tests=<testname>     (Tests matching regular expression)
  * test=<testname>                   (Just that test)
  * debug=<none, valgrind, ddd>
  * build=<debug, advanced, release, notcmalloc>
  * mt=<nbThreads>                    (Number of threads per process -
                                       regression runs 1 process at a time)
  * large                             (large tests too)
  * show_diff                         (Shows text diff)
* regression.tcl update (Updates the diffs)  


++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
## RELEASES

* ./release.tcl Releases the following:

* ./release.tcl
   * Created  dist/surelog_release_notcmalloc.tar.gz
   * Created  dist/surelog_release_tcmalloc.tar.gz
   * Created  dist/surelog_debug_notcmalloc.tar.gz
   * Created  dist/surelog_debug_tcmalloc.tar.gz

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
