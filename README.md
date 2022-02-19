# Surelog

SystemVerilog 2017 Pre-processor, Parser, Elaborator, UHDM Compiler. Provides IEEE Design/TB C/C++ VPI and Python AST API. 

## Goal
This project aims at providing a complete SystemVerilog 2017 front-end: a preprocessor, a parser, an elaborator for both design and testbench. We are aiming at supporting all open-source cores.
* Current status: 
   * Surelog's elaboration trees for [BlackParrot](https://github.com/black-parrot/black-parrot), [Ariane](https://github.com/lowRISC/ariane) cores are equivalent with Verilator's elaboration tree. 
   * [Ibex](https://github.com/lowRISC/ibex) and [Earlgrey](https://github.com/lowRISC/opentitan) completely Synthesizes and runs in Hardware with the Surelog/UHDM/Yosys flow. 

## Applications

Linter, Simulator, Synthesis tool, Formal tools can use this front-end. They either can be developed as plugins (linked with) or use this front-end as an intermediate step of their compilation flows using the on-disk serialized models (UHDM).

## Presentation
* [WOSET 2020 UHDM (& Surelog) Paper and Presentation](https://woset-workshop.github.io/WOSET2020.html#article-10)

## Contributing to this project

This project is open to contributions from any users! From the commercial vendor to the Verilog enthousiast, all are welcome.
We started maintaning a list of ideas for contribution under [Help Wanted](https://github.com/alainmarcel/Help_Wanted)

## Features

 * The preprocessor and the parser use Antlr 4.72 as a parser generator.
 * The preprocessor and the parser ASTs are made persistent on disk using Google Flatbuffers, enabling incremental compilation.
 * The tool is built thread safe and performs multithread parsing.
 * Large files/modules/packages are splitted for multi-threading compilation.
 * Surelog accepts IEEE Simulator-compliant project specification.
 * Surelog issues Errors/Warning/Info/Notes about language compliance.
 * Surelog allows for pre-compiled packages (UVM,...).
 * A comprehensive Python API allows to:
    * listen or visit the Parser grammar and create custom linting rules
    * Visit the design data model and create custom linting rules
    * Customize the message formats
    * Waive messages
 * Surelog creates a [UHDM](https://github.com/alainmarcel/UHDM/) compiled database of the design that can be read by 3rd party tools (Synthesis, Simulator, Linter, Formal...) using the Standard VPI API.

## Build instructions and test:

 * Read [`INSTALL`](INSTALL.md)

```bash
If you had a previous install, remove it first:
  make uninstall  (PREFIX=...)

  make
or
  make debug
or
  make release_no_tcmalloc (For no tcmalloc)
or
  make release_with_python
  
make install (/usr/local/bin and /usr/local/lib/surelog by default,
              use PREFIX= for alternative location)
```

For more build/test options and system requirements for building see
[`src/README`](src/README.md) file.

## Use Surelog as an external package with CMake

For your project to use Surelog as an external module, you need to tell CMake where to find Surelog. Note that CMake expects the module directory organized a certain way and Surelog's installation step does that so make sure to run that. You can provide the path to CMake in few different ways -

1. By updating `CMAKE_MODULE_PATH` variable in your project's CMakeLists.txt file by adding the following lines -

```
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} <absolute or relative path to surelog installation folder>)
find_package(Surelog)
```

2. By providing the location of the surelog installation with the `find_package` command itself, as in the following -
```
find_package(Surelog PATHS <absolute or relative path to surelog installation folder>)
```

3. By providing the location of the surelog installation as a command line parameter when invoking CMake -
```
cmake -DSurelog_DIR=<absolute or relative path to surelog installation folder> -S . -B out
```

For additional help, refer to cmake documentation on external modules.

Once CMake successfully finds Surelog, all you would need is to add the following line after the call to `add_library/add_executable` in your CMakeLists.txt file.
```
target_link_libraries(<your project name> surelog)
```

## Usage

### Surelog commands

 * The executable is located here:
   * build/bin/surelog  (Release build)
   * dbuild/bin/surelog (Debug build)
   * /usr/local/bin/surelog (After install)

 * STANDARD VERILOG COMMAND LINE:
 ```
   -f <file>             Accepts a file containing command line arguments
   -v <file>             Library file
   -sv <file>            Forces this file to be parsed as a SystemVerilog file
   -sverilog             Forces all files to be parsed as SystemVerilog files
   -y <path>             Library directory
   +incdir+<dir>[+<dir>...]  Specifies include paths
   -Idir                 Specifies include paths
   +libext+<extname>+... Specifies the library extensions
   <file>.v              Verilog File
   <file>.sv             SystemVerilog File
   +liborder             Lib Order option (ignored)
   +librescan            Lib Rescan option (ignored)
   +libverbose           Lib Verbose option (ignored)
   +nolibcell            No Lib Cell option (ignored)
   +define+name=value[+name=value...] Defines a macro and optionally its value
   -L <libName>          Defines library compilation order
   -map <mapFile>        Specifies a library mapping file (multiple -map options supported)
   -cfgfile <confiFile>  Specifies a configuration file (multiple -cfgFile options supported)
   -cfg <configName>     Specifies a configuration to use (multiple -cfg options supported)
   -Dvar=value           Same as env var definition for -f files var substitution
   -Pparameter=value     Overrides a toplevel module parameter
```   
 * FLOWS OPTIONS:
 ```
   -fileunit             Compiles each Verilog file as an independent compilation unit (under slpp_unit/ if -writepp used)
   -diffcompunit         Compiles both all files as a whole unit and separate compilation units to perform diffs
   -parse                Parse/Compile/Elaborate the files after pre-processing step
   -top/--top-module <module> Top level module for elaboration (multiple cmds ok)
   -noparse              Turns off Parsing & Compilation & Elaboration
   -nocomp               Turns off Compilation & Elaboration
   -noelab               Turns off Elaboration
   -parseonly            Only Parses, reloads Preprocessor saved db
   -elabuhdm             Forces UHDM/VPI Full Elaboration/Uniquification, default is the Folded Model.
                         A client application can elect to perform the full elaboration after reading back the UHDM db by invoking the Elaborator listener.
   -batch <batch.txt>    Runs all the tests specified in the file in batch mode. Tests are expressed as one full command line per line.
   -pythonlistener       Enables the Parser Python Listener
   -pythonlistenerfile <script.py> Specifies the AST python listener file
   -pythonevalscriptperfile <script.py>  Eval the Python script on each source file (Multithreaded)
   -pythonevalscript <script.py> Eval the Python script at the design level
   -nopython             Turns off all Python features, including waivers
   -withpython           Turns on all Python features, including waivers (Requires to build with python (SURELOG_WITH_PYTHON=1)
   -strictpythoncheck    Turns on strict Python checks
   -mt/--threads <nb_max_treads>   0 up to 512 max threads, 0 or 1 being single threaded, if "max" is given, the program will use one thread per core on the host
   -mp <nb_max_processes> 0 up to 512 max processes, 0 or 1 being single process
   -lowmem               Minimizes memory high water mark (uses multiple staggered processes for preproc, parsing and elaboration)
   -split <line number>  Split files or modules larger than specified line number for multi thread compilation
   -timescale=<timescale> Specifies the overall timescale
   -nobuiltin            Do not parse SV builtin classes (array...)
```
 * YOSYS AND VERILATOR FEATURES:
   To enable feature:
   ```
   --enable-feature=<feature1>,<feature2>

   ```
   To disable feature:
   ```
   --disable-feature=<feature1>,<feature2>
   ```
   Possible features:
   ```
   parametersubstitution	Disables substitution of assignment patterns in parameters

   ```
 * TRACES OPTIONS:
 ```
   -d <int>              Debug <level> 1-4, lib, ast, inst, incl, uhdm, coveruhdm
   -nostdout             Mutes Standard output
   -verbose              Gives verbose processing information
   -profile              Gives Profiling information
```
 * OUTPUT OPTIONS:
``` 
   -l <file>             Specifies log file, default is surelog.log under output dir
   -odir/--Mdir <dir>    Specifies the output directory, default is ./
   -writeppfile <file>   Writes out Preprocessor output in file (all compilation units will override this file)
   -writepp              Writes out Preprocessor output (all compilation units will generate files under slpp_all/ or slpp_unit/)
   -lineoffsetascomments Writes the preprocessor line offsets as comments as opposed as parser directives
   -nocache              Default allows to create a cache for include files, this option prevents it
   -cache <dir>          Specifies the cache directory, default is slpp_all/cache or slpp_unit/cache
   -createcache          Create cache for precompiled packages
   -filterdirectives     Filters out simple directives like default_nettype in pre-processor's output
   -filterprotected      Filters out protected regions in pre-processor's output
   -filtercomments       Filters out comments in pre-processor's output
   -outputlineinfo       Outputs SLline directives in pre-processor's output
   -pploc                Output message location in terms of post preprocessor location
   -noinfo               Filters out INFO messages
   -nonote               Filters out NOTE messages
   -nowarning            Filters out WARNING messages
   -synth                Reports non-synthesizable constructs
   -o <path>             Turns on all compilation stages, produces all outputs under that path
   -cd <dir>             Internally change directory to <dir>
   -exe <command>        Post execute a system call <command>, passes it the preprocessor file list.
   --help                This help
   --version             Surelog version and build date
```   
 * RETURN CODE
``` 
   Bit mask the return code, more than 1 bit can be on.
     0   - No issues
     0x1 - Fatal error(s)
     0x2 - Syntax error(s)
     0x4 - Error(s)
```
### C++ API

 * Surelog comes in the form of a library libsurelog.a and can be linked to an executalble.
 * Extensive API is provided to browse:
   * the preprocessor file contents in AST form,
   * the post-parsing file contents in AST form,
   * the non-elaborated and elaborated design/testbench data model.
   * the UHDM or IEEE VPI Object Model.
 * Creating your own executable using libsurelog.a is discussed in [`src/README`](src/README.md) file.
 * Two examples executable file (hellosureworld.cpp and hellouhdm.cpp) illustrate how to navigate the Surelog internal data structure or the UHDM "VPI Standard Object Model" of the design using the libsurelog.a library.

### Python API

 * By default Surelog does not build the Python API, See  [`src/README`](src/README.md) 
 * The file [`slformatmsg.py`](src/API/slformatmsg.py) illustrates how messages can be reformated.
   * Place a modified version of this file either in the execution directory, or install directory /usr/local/lib/surelog/python

 * The file [`src/API/slSV3_1aPythonListener.py`](src/API/slSV3_1aPythonListener.py) illustrates how a listener can be created to listen to the Parser AST.
   * Place a modified version of this file either in the execution directory, or install directory /usr/local/lib/surelog/python

 * A simple example of creating a new error message and generating errors can be found here: [`python_listener.py`](src/API/python_listener.py)

 * A simple example for design-level data model exploration can be found here: [`myscriptPerDesign.py`](tests/UnitPython/myscriptPerDesign.py)

 * The complete Python API is described in the following files: [`SLAPI.h`](src/API/SLAPI.h) [`vobjecttypes`](src/API/vobjecttypes.py)

 * Waivers can be installed in slwaivers.py files in the execution directory or install directory /usr/local/lib/surelog/python

### Large design compilation on Linux
 * It is recommanded to use the -lowmem -mp <nb processor> options in conjunction for large designs.
 * The preprocessing will occur using one process, but the parsing will occur using multiple processes.
 * The elaboration and UHDM creation will use a single process.
 * Surelog spawns sub-Surelog processes to achieve the overall compilation.
 * Or course don't use the -nocache option to benefit from incremental compilation and reuse cached parsed files 

### Batch mode operations

  * A utility script [`tests/create_batch_script.tcl`](tests/create_batch_script.tcl) generates batch command files for large unit test regressions. See the script's internal help.

## Similar projects:
* [Surelog/UHDM/Yosys/Verilator](https://github.com/chipsalliance/UHDM-integration-tests) Full SystemVerilog Synthesis / Simulation flow
* [UHDM](https://github.com/alainmarcel/UHDM/) - Full SystemVerilog (VHDL later) VPI API for interfacing with 3rd party tools
* [hdlConvertor](https://github.com/Nic30/hdlConvertor/) - SystemVerilog and VHDL parser, preprocessor and code generator for Python/C++ written in C++
* [cl-vhdl](https://github.com/mabragor/cl-vhdl) - lisp, Parser of VHDL into lisp-expressions
* [HDL_ANTLR4](https://github.com/denisgav/HDL_ANTLR4) - C# projects that use ANTLR4 library to analyse VHDL and Verilog code
* [hdlparse](https://github.com/kevinpt/hdlparse/) - vhdl/verilog parser in python
* [ieee1800_2017](https://github.com/veriktig/ieee1800_2017) - Java, SystemVerilog preprocessor
* [Pyverilog](https://github.com/PyHDI/Pyverilog) - python verilog toolkit
* [pyVHDLParser](https://github.com/Paebbels/pyVHDLParser) - python vhdl parser with 2008 support
* [rust_hdl](https://github.com/kraigher/rust_hdl) - rust vhdl 2008 parser
* [slang](https://github.com/MikePopoloski/slang) - Parser and compiler library for SystemVerilog.
* [sv-parser](https://github.com/dalance/sv-parser) - Rust, SystemVerilog parser library fully compliant with IEEE 1800-2017
* [systemc-clang](https://github.com/anikau31/systemc-clang) - SystemC Parser using the Clang Front-end
* [v2sc](https://github.com/denisgav/v2sc) - vhdl to systemc
* [veelox](https://github.com/martinda/veelox) - Java+ANTLR,  An experiment in SystemVerilog Preprocessing
* [verilog-parser](https://github.com/ben-marshall/verilog-parser) - A Flex/Bison Parser for the IEEE 1364-2001 Verilog Standard.
* [vbpp](https://github.com/balanx/vbpp) - C, Verilog PreProcessor
* [tree-sitter-verilog](https://github.com/tree-sitter/tree-sitter-verilog) - JS, Verilog grammar for tree-sitter
* [Verilog-Perl](https://metacpan.org/pod/Verilog-Perl)
* [vpp.pl](https://www.beyond-circuits.com/wordpress/vpp-pl-man-page/) - verilog preprocessor with integrated Perl
* [sv2v](https://github.com/zachjs/sv2v)- Haskell, SystemVerilog to Verilog
