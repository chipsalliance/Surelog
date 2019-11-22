#include "CommandLine/CommandLineParser.h"
#include "SourceCompile/SymbolTable.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/Compiler.h"
#include "ErrorReporting/ErrorContainer.h"
#include "ErrorReporting/Report.h"
#include "ErrorReporting/Waiver.h"

#include "Surelog.h"

SURELOG::scompiler* SURELOG::start_compiler (SURELOG::CommandLineParser* clp) {
  Compiler* the_compiler = new SURELOG::Compiler(clp, clp->getErrorContainer(),
						 clp->getSymbolTable());
  bool status = the_compiler->compile();
  if (!status)
    return nullptr;
  return (SURELOG::scompiler*) the_compiler;          
}

SURELOG::Design* SURELOG::get_design(SURELOG::scompiler* the_compiler) {
  if (the_compiler)
    return ((SURELOG::Compiler*) the_compiler)->getDesign();
  return nullptr;
}

void SURELOG::shutdown_compiler(SURELOG::scompiler* the_compiler) {
  delete (SURELOG::Compiler*) the_compiler;
}

