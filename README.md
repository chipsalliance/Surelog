# Surelog
System Verilog 2017 Pre-processor, Parser 

# Goal
This project aims at providing a complete System Verilog 2017 front-end: a preprocessor, a parser, an elaborator for both design and testbench. 

# Applications

Linter, Simulator, Synthesys tool, Formal tools can use this front-end and be developed either as plugins (linked with) or use this front-end as an intermediate step of their compilation flows using the on-disk memory models (down-converter).

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
```
```bash
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
   * +define+name=value[+name=value...]
   *                      Defines a macro and optionally its value
   * -L <libName>          Defines library compilation order
   * -map <mapFile>        Specifies a library mapping file (multiple -map options supported)
   * -cfgfile <confiFile>  Specifies a configuration file (multiple -cfgFile options supported)
   * -cfg <configName>     Specifies a configuration to use (multiple -cfg options supported)
   * -Dvar=value           Same as env var definition for -f files var substitution
 * FLOWS OPTIONS:
   * -fileunit             Compiles each Verilog file as an independent
   *                       compilation unit (under slpp_unit/ if -writepp used)
   * -diffcompunit         Compiles both all files as a whole unit and
   *                       separate compilation units to perform diffs
   * -parse                Parse/Compile/Elaborate the files after pre-processing step
   * -nocomp               Turns off Compilation & Elaboration
   * -noelab               Turns off Elaboration
   * -pythonlistener       Enables the Parser Python Listener
   * -pythonlistenerfile <script.py> Specifies the AST python listener file
   * -pythonevalscriptperfile <script.py>  Eval the Python script on each source file (Multithreaded)
   * -pythonevalscript <script.py> Eval the Python script at the design level
   * -nopython             Turns off all Python features, including waivers
   * -strictpythoncheck    Turns on strict Python checks
   * -mt <nb_max_treads>   0 up to 512 max threads, 0 or 1 being single threaded,
   *                       if "max" is given, the program will use one thread
   *                       per core on the host
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
   * -writeppfile <file>   Writes out Preprocessor output in file
   *                      (all compilation units will override this file)
   * -writepp              Writes out Preprocessor output (all compilation
   *                       units will generate files under slpp_all/ or slpp_unit/)
   * -lineoffsetascomments Writes the preprocessor line offsets as comments as opposed as parser directives
   * -nocache              Default allows to create a cache for include files, this option prevents it
   *  -cache <dir>          Specifies the cache directory, default is slpp_all/cache or slpp_unit/cache
   * -createcache          Create cache for precompiled packages
   * -filterdirectives     Filters out simple directives like
   *                      `default_nettype in pre-processor's output
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

