# Surelog
System Verilog 2017 Pre-processor, Parser 

# Goal
This project aims at providing a complete System Verilog 2017 front-end: a preprocessor, a parser, an elaborator for both design and testbench. 

# Applications

Linter, Simulator, Synthesis tool, Formal tools can use this front-end. They either can be developed as plugins (linked with) or use this front-end as an intermediate step of their compilation flows using the on-disk serialized models.

# Contributing to this project

This project is open to contributions from any users! From the commercial vendor to the Verilog enthousiast, all are welcome.

# Features

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

# Build instructions and test: 

 * Read [`INSTALL`](INSTALL.md)

```bash
make
make install (/usr/local/bin and /usr/local/lib/surelog by default, use DESTDIR= for alternative locations)
```

For more build/test options and system requirements for building see
[`src/README`](src/README.md) file.

# Surelog commands
 * The executable is located here (If not installed in:
   * build/dist/Release/surelog

 * STANDARD VERILOG COMMAND LINE:
   * -f <file>             Accepts a file containing command line arguments
   * -v <file>             Library file
   * -y <path>             Library directory
   * +incdir+<dir>[+<dir>...]  Specifies include paths
   * -Idir                 Specifies include paths
   * +libext+<extname>+... Specifies the library extensions
   * <file>.v              Verilog File
   * <file>.sv             System Verilog File
   * +liborder             Lib Order option (ignored)
   * +librescan            Lib Rescan option (ignored)
   * +libverbose           Lib Verbose option (ignored)
   * +nolibcell            No Lib Cell option (ignored)
   * +define+name=value[+name=value...] Defines a macro and optionally its value
   * -L <libName>          Defines library compilation order
   * -map <mapFile>        Specifies a library mapping file (multiple -map options supported)
   * -cfgfile <confiFile>  Specifies a configuration file (multiple -cfgFile options supported)
   * -cfg <configName>     Specifies a configuration to use (multiple -cfg options supported)
   * -Dvar=value           Same as env var definition for -f files var substitution
 * FLOWS OPTIONS:
   * -fileunit             Compiles each Verilog file as an independent compilation unit (under slpp_unit/ if -writepp used)
   * -diffcompunit         Compiles both all files as a whole unit and separate compilation units to perform diffs
   * -parse                Parse/Compile/Elaborate the files after pre-processing step
   * -nocomp               Turns off Compilation & Elaboration
   * -noelab               Turns off Elaboration
   * -pythonlistener       Enables the Parser Python Listener
   * -pythonlistenerfile <script.py> Specifies the AST python listener file
   * -pythonevalscriptperfile <script.py>  Eval the Python script on each source file (Multithreaded)
   * -pythonevalscript <script.py> Eval the Python script at the design level
   * -nopython             Turns off all Python features, including waivers
   * -strictpythoncheck    Turns on strict Python checks
   * -mt <nb_max_treads>   0 up to 512 max threads, 0 or 1 being single threaded, if "max" is given, the program will use one thread per core on the host
   * -split <line number>  Split files or modules larger than specified line number for multi thread compilation
   * -timescale=<timescale> Specifies the overall timescale
   * -nobuiltin            Do not parse SV builtin classes (array...)

 * TRACES OPTIONS:
   * -d <int>              Debug <level> 1-4, lib, ast, inst, incl
   * -nostdout             Mutes Standard output
   * -verbose              Gives verbose processing information
   * -profile              Gives Profiling information
   * -l <file>             Specifies log file, default is surelog.log under output dir

 * OUTPUT OPTIONS:
   * -odir <dir>           Specifies the output directory, default is ./
   * -writeppfile <file>   Writes out Preprocessor output in file (all compilation units will override this file)
   * -writepp              Writes out Preprocessor output (all compilation units will generate files under slpp_all/ or slpp_unit/)
   * -lineoffsetascomments Writes the preprocessor line offsets as comments as opposed as parser directives
   * -nocache              Default allows to create a cache for include files, this option prevents it
   * -cache <dir>          Specifies the cache directory, default is slpp_all/cache or slpp_unit/cache
   * -createcache          Create cache for precompiled packages
   * -filterdirectives     Filters out simple directives like default_nettype in pre-processor's output
   * -filterprotected      Filters out protected regions in pre-processor's output
   * -filtercomments       Filters out comments in pre-processor's output
   * -outputlineinfo       Outputs SLline directives in pre-processor's output
   * -pploc                Output message location in terms of post preprocessor location
   * -noinfo               Filters out INFO messages
   * -nonote               Filters out NOTE messages
   * -nowarning            Filters out WARNING messages
   * -o <path>             Turns on all compilation stages, produces all outputs under that path
   * --help                This help 
   * --version             Surelog version and build date
 * RETURN CODE
   * Bit mask the return code, more than 1 bit can be on.
   * 0   - No issues
   * 0x1 - Fatal error(s)
   * 0x2 - Syntax error(s)
   * 0x4 - Error(s)
   
### Python API

 * The file [`slformatmsg.py`](src/API/slformatmsg.py) illustrates how messages can be reformated.
   * Place a modified version of this file either in the execution directory, or install directory /usr/local/lib/surelog/python

 * The file [`src/API/slSV3_1aPythonListener.py`](src/API/slSV3_1aPythonListener.py) illustrates how a listener can be created to listen to the Parser AST.
   * Place a modified version of this file either in the execution directory, or install directory /usr/local/lib/surelog/python

 * A simple example of creating a new error message and generating errors can be found here: [`python_listener.py`](src/API/python_listener.py)

 * A simple example for design-level data model exploration can be found here: [`myscriptPerDesign.py`](tests/UnitPython/myscriptPerDesign.py)
 
 * The complete Python API is described in the following files: [`SLAPI.h`](src/API/SLAPI.h) [`vobjecttypes`](src/API/vobjecttypes.py)

 * Waivers can be installed in slwaivers.py files in the execution directory or install directory /usr/local/lib/surelog/python

### Creating your own executable using libsurelog.a
  * This is discussed in [`src/README`](src/README.md) file.

### Similar projects:

* [hdlConvertor](https://github.com/Nic30/hdlConvertor/) - System Verilog and VHDL parser, preprocessor and code generator for Python/C++ written in C++ 
* [cl-vhdl](https://github.com/mabragor/cl-vhdl) - lisp, Parser of VHDL into lisp-expressions 
* [HDL_ANTLR4](https://github.com/denisgav/HDL_ANTLR4) - C# projects that use ANTLR4 library to analyse VHDL and Verilog code
* [hdlparse](https://github.com/kevinpt/hdlparse/) - vhdl/verilog parser in python
* [ieee1800_2017](https://github.com/veriktig/ieee1800_2017) - Java, SystemVerilog preprocessor
* [Pyverilog](https://github.com/PyHDI/Pyverilog) - python verilog toolkit
* [pyVHDLParser](https://github.com/Paebbels/pyVHDLParser) - python vhdl parser with 2008 support
* [rust_hdl](https://github.com/kraigher/rust_hdl) - rust vhdl 2008 parser
* [slang](https://github.com/MikePopoloski/slang) - Parser and compiler library for SystemVerilog.
* [sv-parser](https://github.com/dalance/sv-parser) - Rust, SystemVerilog parser library fully complient with IEEE 1800-2017
* [systemc-clang](https://github.com/anikau31/systemc-clang) - SystemC Parser using the Clang Front-end
* [v2sc](https://github.com/denisgav/v2sc) - vhdl to systemc
* [veelox](https://github.com/martinda/veelox) - Java+ANTLR,  An experiment in SystemVerilog Preprocessing 
* [verilog-parser](https://github.com/ben-marshall/verilog-parser) - A Flex/Bison Parser for the IEEE 1364-2001 Verilog Standard.
* [vbpp](https://github.com/balanx/vbpp) - C, Verilog PreProcessor
* [tree-sitter-verilog](https://github.com/tree-sitter/tree-sitter-verilog) - JS,  Verilog grammar for tree-sitter 
* [Verilog-Perl](https://metacpan.org/pod/Verilog-Perl)
* [vpp.pl](https://www.beyond-circuits.com/wordpress/vpp-pl-man-page/) - verilog preprocessor with integrated Perl
* [sv2v](https://github.com/zachjs/sv2v)- Haskell, SystemVerilog to Verilog
