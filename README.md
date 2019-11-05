# Surelog
System Verilog 2017 Pre-processor, Parser 

# Goal
This project aims at providing a complete System Verilog 2017 front-end: a preprocessor, a parser, an elaborator for both design and testbench. 

# Applications

Linter, Simulator, Synthesys tool, Formal tools can use this front-end and be developed either as plugins (linked with) or use this front-end as an intermediate step of their compilation flows using the on-disk memory models (down-converter).

# Contributing to this project

This project is open to contributions from any user! From the commercial vendor to the Verilog enthousiast are welcome.

# Features

 * The preprocessor and the parser use Antlr 4.72 as a parser generator.
 * The preprocessor and the parser ASTs are made persistent on disk using Google Flatbuffers, enabling incremental compilation.
 * The tool is built thread safe and performs multithread parsing.
 * Large files/modules/packages are splitted for multi-threading compilation.
 * Surelog accepts IEEE Simulator-compliant project specification.
 * Surelog issues Errors/Warning/Info/Notes about language compliance.
 * Surelog allows for pre-compiled packages (UVM,...).

# Build instructions and test: 

```bash
make
```

For more build/test options and system requirements for building see
[`SVIncCompil/README`](./SVIncCompil/README.md) file.




