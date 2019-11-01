# Surelog
System Verilog 2017 Pre-processor, Parser 

# Goal
This project aims at providing a complete System Verilog 2017 front-end: a preprocessor, a parser, an elaborator for both design and testbench 

# Applications

Linter, Simulator, Synthesys tool, Formal tools can use this front-end and be developed as plugins or use this front-end as an intermediate step of their compilation flows.

# Features

The preprocessor and the parser use Antlr 4.72 as a parser generator.

The preprocessor and the parser ASTs are made persistent on disk using Google Flatbuffers, enabling incremental compilation.

The whole tool is built thread safe and performs multithread parsing.

Large files/module/packages are splitted for multi-threading compilation.



