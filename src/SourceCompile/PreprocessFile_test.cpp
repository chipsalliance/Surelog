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

#include <string>
#include <string_view>
#include <vector>

#include "SourceCompile/PreprocessHarness.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

using ::testing::ElementsAre;

namespace SURELOG {
namespace {
TEST(PreprocessTest, PreprocessWithoutPPTokens) {
  PreprocessHarness harness;
  const std::string res = harness.preprocess("module top(); endmodule");
  EXPECT_EQ(res, "module top(); endmodule");
}

TEST(PreprocessTest, PreprocessSingleParameterExpansion) {
  PreprocessHarness harness;
  const std::string res = harness.preprocess(R"(
`define FOO(a) a*2
module top();
  assign b = `FOO(c);
endmodule)");

  EXPECT_EQ(res, R"(
module top();
  assign b = c*2;
endmodule)");
}

TEST(PreprocessTest, PreprocessTwoParameterExpansion) {
  PreprocessHarness harness;
  const std::string res = harness.preprocess(R"(
`define BAR(a, b) (a)*2+( b )
module top();
  assign b = `BAR(3 * c, 2*d);
endmodule)");

  EXPECT_EQ(res, R"(
module top();
  assign b = (3 * c)*2+( 2*d );
endmodule)");
}

TEST(PreprocessTest, PreprocessMacroExpansionInMacroCall) {
  PreprocessHarness harness;
  const std::string res = harness.preprocess(R"(
`define FOURTYTWO 42
`define BAR(a) a * 3
module top();
  assign b = `BAR(`FOURTYTWO);
endmodule)");

  EXPECT_EQ(res, R"(
module top();
  assign b = 42 * 3;
endmodule)");
}

TEST(PreprocessTest, PreprocessMacroExpansionWithDefaultParameter) {
  PreprocessHarness harness;
  const std::string res = harness.preprocess(R"(
`define FOO(a = 42) a * 2
module top();
  assign b = `FOO(1);
  assign c = `FOO();  // Default applies
endmodule)");

  EXPECT_EQ(res, R"(
module top();
  assign b = 1 * 2;
  assign c = 42 * 2;  // Default applies
endmodule)");
}

}  // namespace
}  // namespace SURELOG
