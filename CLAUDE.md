# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Surelog is a SystemVerilog 2017 pre-processor, parser, elaborator, and UHDM compiler. It provides IEEE Design/TB C/C++ VPI and Python AST APIs for use by linters, simulators, synthesis tools, and formal verification tools.

## Build Commands

### Primary Build Commands
```bash
# Standard release build
make -j$(nproc)

# Debug build
make debug

# Release build with Python support
make release_with_python

# Release build without tcmalloc (for compatibility)
make release_no_tcmalloc

# Shared library build
make release-shared

# Clean build artifacts
make clean

# Install to system (default: /usr/local)
make install
# Custom prefix: PREFIX=/path/to/install make install
```

### Testing Commands

**IMPORTANT: The official regression harness is the Python script
`scripts/regression.py`, NOT `tests/regression.tcl` (the tcl script is
legacy).** All golden-log generation, comparison, and CI use `regression.py`.

```bash
# Run the whole regression (or a subset) against a given build's surelog binary.
# `--filters` takes one or more regexes matched against test names.
# `--build-dirpath` points at the dir containing bin/surelog (relative to the
# workspace root, or absolute).
python3 scripts/regression.py run --filters <TestNameRegex> --build-dirpath <build>

# Regenerate/refresh the golden .log for the matched test(s) in place:
python3 scripts/regression.py update --filters <TestNameRegex> --build-dirpath <build>

# Modes: run | report | update | extract.  Tests are auto-discovered by
# globbing tests/<Name>/<Name>.sl (and third_party/tests) — no manifest.
# Golden logs are stored as tests/<Name>/<Name>.log with paths normalized to
# ${SURELOG_DIR}.  When surelog lives in the uhdm2rtlil superbuild, use
# --build-dirpath /home/alain/uhdm2rtlil/build/third_party/Surelog

# Legacy tcl harness (avoid — kept only for reference):
#   cd build && tclsh ../tests/regression.tcl diff_mode show_diff

# Run unit tests
make test/unittest

# Run specific test manually
cd build && ../bin/surelog ../tests/<TestName>/dut.sv

# Run valgrind memory checks
make test/valgrind

# Coverage analysis
make test/unittest-coverage
```

## Architecture Overview

### Core Components

**Parser Infrastructure** (`src/parser/`, `grammar/`)
- ANTLR 4.10 based SystemVerilog parser
- Separate lexers/parsers for preprocessing and main parsing
- Multi-threaded parsing with file splitting for large modules

**Design Compilation** (`src/DesignCompile/`)
- `CompileDesign`: Main design compilation orchestrator
- `CompileModule`: Module-level compilation
- `CompileExpression`: Expression evaluation and compilation
- `UhdmWriter`: UHDM database generation
- `ElaborationStep`: Design elaboration phases

**Source Processing** (`src/SourceCompile/`)
- `PreprocessFile`: Preprocessor implementation
- `ParseFile`: File parsing coordination
- `Compiler`: Main compilation driver
- `SymbolTable`: Symbol management

**Data Model** (`src/Design/`)
- `Design`: Top-level design container
- `ModuleDefinition`/`ModuleInstance`: Module hierarchy
- `FileContent`: Parsed file representation
- `VObject`: Parse tree nodes
- `DataType`, `Signal`, `Parameter`: Design elements

**Error Handling** (`src/ErrorReporting/`)
- Multi-level error reporting (Fatal/Error/Warning/Info/Note)
- Waiver system for filtering messages
- Location tracking across preprocessing and parsing

### Key Design Patterns

- **Incremental Compilation**: Cap'n Proto serialization enables caching of preprocessed and parsed files
- **Separate Compilation Flow**: Supports independent compilation units with final linking phase
- **Thread Safety**: Parser and compilation stages are thread-safe for parallel processing
- **VPI Standard API**: UHDM output follows IEEE VPI standard for tool integration

## Common Development Tasks

### Running Surelog

```bash
# Basic parsing
build/bin/surelog <file>.sv -parse

# With preprocessing output
build/bin/surelog <file>.sv -writepp -parse

# Generate UHDM database
build/bin/surelog <file>.sv -parse -elabuhdm

# Multi-file compilation with includes
build/bin/surelog -f <filelist> +incdir+<dir1>+<dir2> -parse

# Top-level elaboration
build/bin/surelog <files> -top <module_name> -elabuhdm
```

### Debugging Options

```bash
# Debug levels (1-4) and categories
-d <level>
-d uhdm      # UHDM generation debug
-d ast       # AST debug  
-d inst      # Instance debug
-d incl      # Include file debug

# Profiling
-profile

# Verbose output
-verbose
```

## Code Formatting

Before submitting code changes:
```bash
clang-format -i -style=Google -sort-includes=false <files>
```

## Python API Usage

The Python API requires building with Python support (`make release_with_python`). Python scripts can be used for:
- Custom linting rules via AST traversal
- Message formatting customization (`slformatmsg.py`)
- Design analysis (`pythonevalscript`)
- Waivers configuration (`slwaivers.py`)

## Debugging New Issues - ScratchPad Test

For debugging new issues, use the primary test configuration from VSCode launch.json:

```bash
# From workspace root:
dbuild/bin/surelog -parse tests/ScratchPad.sv -elabuhdm -d inst -synth -d ast -d uhdm -d uhdmstats -d vpi_ids -replay -nobuiltin
```

This ScratchPad.sv file is the primary test file for debugging new issues. The command includes comprehensive debug flags for:
- `-elabuhdm`: Forces UHDM/VPI Full Elaboration/Uniquification
- `-d inst`: Instance debugging
- `-d ast`: AST debugging
- `-d uhdm`: UHDM generation debugging
- `-d uhdmstats`: UHDM statistics
- `-d vpi_ids`: VPI identifier tracking
- `-replay`: Replay mode
- `-nobuiltin`: Disable built-in types
- `-synth`: Synthesis mode

## Important Notes

- Thread count can be controlled with `-mt <threads>` (0 = single-threaded, "max" = one per core)
- Large designs benefit from `-lowmem -mp <processes>` options
- Cache invalidation happens automatically based on file timestamps unless `-nohash` is used
- The `-fileunit` flag treats each file as a separate compilation unit
- Return codes use bit masks: 0x1 (Fatal), 0x2 (Syntax Error), 0x4 (Error)