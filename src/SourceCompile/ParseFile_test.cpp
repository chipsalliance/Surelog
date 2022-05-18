/*
 Copyright 2021 Alain Dargelas

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

#include <Surelog/Design/FileContent.h>
#include <Surelog/SourceCompile/ParseFile.h>
#include <Surelog/SourceCompile/ParserHarness.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <gmock/gmock.h>
#include <gtest/gtest.h>

namespace SURELOG {
using ::testing::ElementsAre;

namespace {
TEST(ParserTest, BasicParse) {
  ParserHarness harness;
  {
    auto fC = harness.parse("module top(); assign a = b; endmodule");
    NodeId root = fC->getRootNode();
    NodeId assign = fC->sl_collect(root, slContinuous_assign);
    EXPECT_NE(assign, 0);
  }
  {
    auto fC = harness.parse("module top(); assign a = !b; endmodule");
    NodeId root = fC->getRootNode();
    NodeId assign = fC->sl_collect(root, slContinuous_assign);
    /*
    n<> u<10> t<Net_lvalue> p<17> c<7> s<16> l<1:22> el<1:23>
    n<b> u<11> t<StringConst> p<12> l<1:27> el<1:28>
    n<> u<12> t<Primary_literal> p<13> c<11> l<1:27> el<1:28>
    n<> u<13> t<Primary> p<14> c<12> l<1:27> el<1:28>
    n<> u<14> t<Expression> p<16> c<13> l<1:27> el<1:28>
    n<> u<15> t<Unary_Not> p<16> s<14> l<1:26> el<1:27>
    n<> u<16> t<Expression> p<17> c<15> l<1:26> el<1:28>
    n<> u<17> t<Net_assignment> p<18> c<10> l<1:22> el<1:28>
    n<> u<18> t<List_of_net_assignments> p<19> c<17> l<1:22> el<1:28>
    n<> u<19> t<Continuous_assign> p<20> c<18> l<1:15> el<1:29>
    */
    NodeId List_of_net_assignments = fC->Child(assign);
    NodeId Net_assignment = fC->Child(List_of_net_assignments);
    NodeId Net_lvalue = fC->Child(Net_assignment);
    NodeId Expression = fC->Sibling(Net_lvalue);
    NodeId Unary_Not = fC->Child(Expression);
    EXPECT_EQ(fC->Type(Unary_Not), slUnary_Not);
  }
}
}  // namespace
}  // namespace SURELOG
