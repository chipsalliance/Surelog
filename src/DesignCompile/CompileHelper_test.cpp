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

#include "SourceCompile/SymbolTable.h"
#include "Library/Library.h"
#include "Design/FileContent.h"
#include "ErrorReporting/Error.h"
#include "ErrorReporting/Location.h"
#include "ErrorReporting/Error.h"
#include "ErrorReporting/ErrorDefinition.h"
#include "ErrorReporting/ErrorContainer.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "CommandLine/CommandLineParser.h"
#include "SourceCompile/ParseFile.h"
#include "Testbench/ClassDefinition.h"
#include "SourceCompile/Compiler.h"
#include "DesignCompile/CompileDesign.h"
#include "DesignCompile/ResolveSymbols.h"
#include "DesignCompile/DesignElaboration.h"
#include "DesignCompile/NetlistElaboration.h"
#include "DesignCompile/UVMElaboration.h"
#include "DesignCompile/CompilePackage.h"
#include "DesignCompile/CompileModule.h"
#include "DesignCompile/CompileFileContent.h"
#include "DesignCompile/CompileProgram.h"
#include "DesignCompile/CompileClass.h"
#include "DesignCompile/Builtin.h"
#include "DesignCompile/PackageAndRootElaboration.h"
#include "DesignCompile/UhdmWriter.h"

#include "Design/VObject.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/Compiler.h"
#include "DesignCompile/CompileDesign.h"
#include "Design/FileContent.h"
#include "Expression/ExprBuilder.h"

#include "DesignCompile/CompileHelper.h"
#include "gtest/gtest.h"
#include "gmock/gmock.h"
#include "vpi_visitor.h"

using namespace UHDM;

class MockFileContent : public SURELOG::FileContent {
  public:
    MockFileContent() : FileContent(0, nullptr, nullptr, nullptr, nullptr, 0){};
    void set_objects(std::vector<SURELOG::VObject> objs){m_objects = objs;}
};

UHDM::Serializer sharedSerializer;
class MockCompileDesign : public SURELOG::CompileDesign {
  public:
    MockCompileDesign() : CompileDesign(nullptr) {}
    virtual UHDM::Serializer& getSerializer() override {
      return sharedSerializer;
    }
};
// Need this to get serializer for VpiName, VpiValue etc.
MockCompileDesign cd;

using SURELOG::VObject;

struct CompileHelperTestStruct {
  std::vector<VObject> objects;
  UHDM::tf_call* expected;
  SURELOG::SymbolTable symbols;
  CompileHelperTestStruct(std::vector<VObject> file_content,
                          std::vector<std::string> strings,
                          std::function<UHDM::tf_call*()> exp_init,
                          std::vector<std::function<UHDM::BaseClass*(void)>> initializers
                          )
                           : objects(file_content)
                         {
                           for (auto s : strings)
                             symbols.registerSymbol(s);

                           // Symbol table starts at 1
                           expected = exp_init();

                           VectorOfany* arguments = new VectorOfany;
                           for (auto f : initializers) {
                             // Run initializer function
                             arguments->push_back(f());
                           }

                           expected->Tf_call_args(arguments);
                         }
};

CompileHelperTestStruct testCases[] = {
  {
    // Simplest case: foo();
    {
      // Vector of VObjects
      // n<>    u<19> t<Subroutine_call>   p<20> c<17>       l<3>
      // n<foo> u<17> t<StringConst>       p<19>       s<18> l<3>
      // n<>    u<18> t<List_of_arguments> p<19>             l<3>
      //
      // Constructor call:
      // (nameId, fileId, type, line, parent, definition, child, sibling)
     { 0, 0, VObjectType::slSubroutine_call,   3, 5, 4, 6, 20, 1,  1, 0},
     { 1, 0, VObjectType::slStringConst,       3, 5, 4, 6, 0, 2, 0,  2},
     { 0, 0, VObjectType::slList_of_arguments, 3, 5, 4, 6, 0, 3, 0,  0}
    },
    // Symbol table
    {"foo"},
    // UHDM func_call initializer
    [] () -> UHDM::tf_call* {
      UHDM::func_call* c = sharedSerializer.MakeFunc_call();
      c->VpiName("foo");
      return c;
    },
    // Argument vector initializers
    {},
  },
  {
    // dsp("%d",clk);
    {
      // Vector of VObjects
      // n<> u<0> t<Subroutine_call> p<35> c<1> l<4>
      //    n<dsp> u<1> t<StringConst> p<0> s<2> l<4>
      //    n<> u<2> t<List_of_arguments> p<0> c<3> l<3>
      //        n<> u<3> t<Expression> p<2> c<4> s<7> l<3>
      //            n<> u<4> t<Primary> p<3> c<5> l<3>
      //                n<> u<5> t<Primary_literal> p<4> c<6> l<3>
      //                    n<"%d"> u<6> t<StringLiteral> p<5> l<4>
      //        n<> u<7> t<Expression> p<2> c<8> l<4>
      //            n<> u<8> t<Primary> p<7> c<9> l<4>
      //                n<> u<9> t<Primary_literal> p<8> c<10> l<4>
      //                    n<clk> u<10> t<StringConst> p<9> l<4>
      // Constructor call:
      // (nameId, fileId, type, line, parent, definition, child, sibling)
     { 0, 0, VObjectType::slSubroutine_call,         4, 5, 4, 6, 35,  0,  1, 0},
       { 1, 0, VObjectType::slStringConst,           4, 5, 4, 6, 0,  1,  0, 2},
       { 0, 0, VObjectType::slList_of_arguments,     4, 5, 4, 6, 0,  2,  3, 0},
         { 0, 0, VObjectType::slExpression,          4, 5, 4, 6,  2,  3,  4, 7},
           { 0, 0, VObjectType::slPrimary,           4, 5, 4, 6,  3,  4,  5, 0},
             { 0, 0, VObjectType::slPrimary_literal, 4, 5, 4, 6,  4,  5,  6, 0},
               { 2, 0, VObjectType::slStringLiteral, 4, 5, 4, 6,  5,  6,  0, 0},
         { 0, 0, VObjectType::slExpression,          4, 5, 4, 6,  2,  7,  8, 0},
           { 0, 0, VObjectType::slPrimary,           4, 5, 4, 6,  7,  8,  9, 0},
             { 0, 0, VObjectType::slPrimary_literal, 4, 5, 4, 6,  8,  9, 10, 0},
               { 3, 0, VObjectType::slStringConst,   4, 5, 4, 6,  9, 10,  0, 0},
    },
    // Symbol table
    {"dsp", "%d", "clk"},
    // UHDM func_call initializers
    [] () -> UHDM::tf_call* {
      UHDM::func_call* c = sharedSerializer.MakeFunc_call();
      c->VpiName("dsp");
      return c;
    },
    // Argument vector initializers
    {
      [] () -> UHDM::BaseClass* {
        UHDM::constant* c = sharedSerializer.MakeConstant();
        c->VpiConstType(vpiStringConst);
        c->VpiValue("STRING:%d");
        return c;
      },
      // Variables are not parsed as arguments yet
      [] () -> UHDM::BaseClass* {
        UHDM::ref_obj* c = sharedSerializer.MakeRef_obj();
        c->VpiName("clk");
        return c;
      },
    }
  },
  {
    // $display("Hello");
    {
      // Vector of VObjects
      //n<> u<33> t<Subroutine_call> p<34> c<26> l<4>
      //    n<> u<26> t<Dollar_keyword> p<33> s<27> l<4>
      //    n<display> u<27> t<StringConst> p<33> s<32> l<4>
      //    n<> u<32> t<List_of_arguments> p<33> c<31> l<4>
      //        n<> u<31> t<Expression> p<32> c<30> l<4>
      //            n<> u<30> t<Primary> p<31> c<29> l<4>
      //                n<> u<29> t<Primary_literal> p<30> c<28> l<4>
      //                    n<"Hello"> u<28> t<StringLiteral> p<29> l<4>
      // Constructor call:
      // (nameId, fileId, type, line, parent, definition, child, sibling)
      {0, 0, VObjectType::slSubroutine_call, 4, 5, 4, 6, 0, 0, 1, 0},
      {0, 0, VObjectType::slDollar_keyword, 4, 5, 4, 6, 0, 0, 0, 2},
      {1, 0, VObjectType::slStringConst, 4, 5, 4, 6, 0, 0, 0, 3},
      {0, 0, VObjectType::slList_of_arguments, 4, 5, 4, 6, 0, 0, 4, 0},
      {0, 0, VObjectType::slExpression, 4, 5, 4, 6, 3, 0, 5, 0},
      {0, 0, VObjectType::slPrimary, 4, 5, 4, 6, 4, 0, 6, 0},
      {0, 0, VObjectType::slPrimary_literal, 4, 5, 4, 6, 5, 0, 7, 0},
      {2, 0, VObjectType::slStringLiteral, 4, 5, 4, 6, 6, 0, 0, 0},
    },
    // Symbol table
    {"display", "Hello"},
    // UHDM func_call initializers
    [] () -> UHDM::tf_call* {
      UHDM::sys_func_call* c = sharedSerializer.MakeSys_func_call();
      c->VpiName("$display");
      return c;
    },
    // Argument vector initializers
    {
      [] () -> UHDM::BaseClass* {
        UHDM::constant* c = sharedSerializer.MakeConstant();
        c->VpiConstType(vpiStringConst);
        c->VpiValue("STRING:Hello");
        return c;
      },
    }
  },
  {
    // $display("%d", 0);
    {
      // Vector of VObjects
      //n<> u<37> t<Subroutine_call> p<38> c<26> l<4>
      //    n<> u<26> t<Dollar_keyword> p<37> s<27> l<4>
      //    n<display> u<27> t<StringConst> p<37> s<36> l<4>
      //    n<> u<36> t<List_of_arguments> p<37> c<31> l<4>
      //        n<> u<31> t<Expression> p<36> c<30> s<35> l<4>
      //            n<> u<30> t<Primary> p<31> c<29> l<4>
      //                n<> u<29> t<Primary_literal> p<30> c<28> l<4>
      //                    n<"%d"> u<28> t<StringLiteral> p<29> l<4>
      //        n<> u<35> t<Expression> p<36> c<34> l<4>
      //            n<> u<34> t<Primary> p<35> c<33> l<4>
      //                n<> u<33> t<Primary_literal> p<34> c<32> l<4>
      //                    n<0> u<32> t<IntConst> p<33> l<4>
      {0, 0, VObjectType::slSubroutine_call, 4, 5, 4, 6, 0, 0, 1, 0},
      {0, 0, VObjectType::slDollar_keyword, 4, 5, 4, 6, 0, 0, 0, 2},
      {1, 0, VObjectType::slStringConst, 4, 5, 4, 6, 0, 0, 0, 3},
      {0, 0, VObjectType::slList_of_arguments, 4, 5, 4, 6, 0, 0, 4, 0},
      {0, 0, VObjectType::slExpression, 4, 5, 4, 6, 3, 0, 5, 6},
      {0, 0, VObjectType::slPrimary, 4, 5, 4, 6, 4, 0, 7, 0},
      {0, 0, VObjectType::slPrimary_literal, 4, 5, 4, 6, 5, 0, 8, 0},
      {2, 0, VObjectType::slStringLiteral, 4, 5, 4, 6, 7, 0, 0, 0},
      {0, 0, VObjectType::slExpression, 4, 5, 4, 6, 3, 0, 9, 0},
      {0, 0, VObjectType::slPrimary, 4, 5, 4, 6, 6, 0, 10, 0},
      {0, 0, VObjectType::slPrimary_literal, 4, 5, 4, 6, 9, 0, 11, 0},
      {3, 0, VObjectType::slIntConst, 4, 5, 4, 6, 10, 0, 0, 0},
    },
    // Symbol table
    {"display", "%d", "0"},
    // UHDM func_call initializers
    [] () -> UHDM::tf_call* {
      UHDM::sys_func_call* c = sharedSerializer.MakeSys_func_call();
      c->VpiName("$display");
      return c;
    },
    // Argument vector initializers
    {
      [] () -> UHDM::BaseClass* {
        UHDM::constant* c = sharedSerializer.MakeConstant();
        c->VpiConstType(vpiStringConst);
        c->VpiValue("STRING:%d");
        return c;
      },
      [] () -> UHDM::BaseClass* {
        UHDM::constant* c = sharedSerializer.MakeConstant();
        c->VpiConstType(vpiIntConst);
        c->VpiValue("INT:0");
        return c;
      },
    },
  },
  {
    // $display("Value: %d", 0xFF);
    {
      // Vector of VObjects
      //n<> u<37> t<Subroutine_call> p<38> c<26> l<4>
      //    n<> u<26> t<Dollar_keyword> p<37> s<27> l<4>
      //    n<display> u<27> t<StringConst> p<37> s<36> l<4>
      //    n<> u<36> t<List_of_arguments> p<37> c<31> l<4>
      //        n<> u<31> t<Expression> p<36> c<30> s<35> l<4>
      //            n<> u<30> t<Primary> p<31> c<29> l<4>
      //                n<> u<29> t<Primary_literal> p<30> c<28> l<4>
      //                    n<"Value: %d"> u<28> t<StringLiteral> p<29> l<4>
      //        n<> u<35> t<Expression> p<36> c<34> l<4>
      //            n<> u<34> t<Primary> p<35> c<33> l<4>
      //                n<> u<33> t<Primary_literal> p<34> c<32> l<4>
      //                    n<'hFF> u<32> t<IntConst> p<33> l<4>
      {0, 0, VObjectType::slSubroutine_call, 4, 5, 4, 6, 0, 0, 1, 0},
      {0, 0, VObjectType::slDollar_keyword, 4, 5, 4, 6, 0, 0, 0, 2},
      {1, 0, VObjectType::slStringConst, 4, 5, 4, 6, 0, 0, 0, 3},
      {0, 0, VObjectType::slList_of_arguments, 4, 5, 4, 6, 0, 0, 4, 0},
      {0, 0, VObjectType::slExpression, 4, 5, 4, 6, 3, 0, 5, 6},
      {0, 0, VObjectType::slPrimary, 4, 5, 4, 4, 6, 0, 7, 0},
      {0, 0, VObjectType::slPrimary_literal, 4, 5, 4, 6, 5, 0, 8, 0},
      {2, 0, VObjectType::slStringLiteral, 4, 5, 4, 6, 7, 0, 0, 0},
      {0, 0, VObjectType::slExpression, 4, 5, 4, 6, 3, 0, 9, 0},
      {0, 0, VObjectType::slPrimary, 4, 5, 4, 6, 6, 0, 10, 0},
      {0, 0, VObjectType::slPrimary_literal, 4, 5, 4, 6, 9, 0, 11, 0},
      {3, 0, VObjectType::slIntConst, 4, 5, 4, 6, 10, 0, 0, 0},
    },
    // Symbol table
    {"display", "Value: %d", "'hFF"},
    // UHDM func_call initializers
    [] () -> UHDM::tf_call* {
      UHDM::sys_func_call* c = sharedSerializer.MakeSys_func_call();
      c->VpiName("$display");
      return c;
    },
    // Argument vector initializers
    {
      [] () -> UHDM::BaseClass* {
        UHDM::constant* c = sharedSerializer.MakeConstant();
        c->VpiConstType(vpiStringConst);
        c->VpiValue("STRING:Value: %d");
        return c;
      },
      [] () -> UHDM::BaseClass* {
        UHDM::constant* c = sharedSerializer.MakeConstant();
        c->VpiConstType(vpiIntConst);
        c->VpiValue("INT:255");
        return c;
      },
    },
  },
};

UHDM::design* addCallToDesign(UHDM::tf_call* call) {
  UHDM::Serializer& s = cd.getSerializer();
  design* d = s.MakeDesign();
  d->VpiName("designTF");
  module* m1 = s.MakeModule();
  m1->VpiTopModule(true);
  m1->VpiDefName("M1");
  m1->VpiParent(d);
  m1->VpiFile("fake1.sv");
  m1->VpiLineNo(10);

  initial* init = s.MakeInitial();
  VectorOfprocess_stmt* processes = s.MakeProcess_stmtVec();
  processes->push_back(init);
  begin* begin_block = s.MakeBegin();
  init->Stmt(begin_block);
  VectorOfany* statements = s.MakeAnyVec();

  // Add call to minimal design
  statements->push_back(call);

  begin_block->Stmts(statements);
  m1->Process(processes);

  VectorOfmodule* v1 = s.MakeModuleVec();
  v1->push_back(m1);
  d->AllModules(v1);

  package* p1 = s.MakePackage();
  p1->VpiDefName("P0");
  VectorOfpackage* v3 = s.MakePackageVec();
  v3->push_back(p1);
  d->AllPackages(v3);

  return d;
}

// Currently segfaults. Disbled.
TEST(DISABLED_CompileHelperTest, TestCompileTfCall) {
  SURELOG::CompileHelper dut;
  MockFileContent fc;
  UHDM::Serializer& s = cd.getSerializer();

  for (auto test_case : testCases) {
    fc.set_objects(test_case.objects);
    fc.setSymbolTable(&test_case.symbols);
    UHDM::tf_call* returned = nullptr; dut.compileTfCall(nullptr, &fc,
                                                0,
                                                &cd);

    UHDM::design* expectedDesign = addCallToDesign(test_case.expected);
    UHDM::design* returnedDesign = addCallToDesign(returned);

    vpiHandle hExpected = s.MakeUhdmHandle(UHDM::uhdmdesign, expectedDesign);
    vpiHandle hParsed = s.MakeUhdmHandle(UHDM::uhdmdesign, returnedDesign);

    std::string expected = visit_designs({hExpected});
    std::string parsed = visit_designs({hParsed});
    ASSERT_EQ(parsed, expected);
  }
}
