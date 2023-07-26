/*
 Copyright 2019 Alain Dargelas

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
 */

/*
 * File:   Surelog.h
 * Author: alain
 *
 * Created on November 21, 2019, 10:09 PM
 */

#ifndef SURELOG_SURELOG_H
#define SURELOG_SURELOG_H
#pragma once

// UHDM
#include <uhdm/sv_vpi_user.h>

namespace SURELOG {

class CommandLineParser;
class Design;
struct scompiler;
class AstListener;
class ParseTreeListener;

// Create a compiler session based on the command line options
scompiler* start_compiler(CommandLineParser* clp);

// Surelog internal design representation and AST access
Design* get_design(scompiler* compiler);

// UHDM Database design access (use UHDM SystemVerilog Object Model schema to
// navigate) see: third_party/Verilog_Object_Model.pdf
//      third_party/UHDM/include/
//      third_party/UHDM/headers/
vpiHandle get_uhdm_design(scompiler* compiler);

// Terminate the compiler session, cleanup internal datastructures,
// Purges UHDM and VPI from memory,
// this invalidates any UHDM/VPI pointers the client application might still
// use!
void shutdown_compiler(scompiler* compiler);

void walk_ast(scompiler* compiler, AstListener* listener);
void walk_ast(scompiler* compiler, ParseTreeListener* listener);

}  // namespace SURELOG

#endif  // SURELOG_SURELOG_H
