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

#include <Surelog/SourceCompile/PreprocessHarness.h>
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

namespace SURELOG {
using ::testing::ElementsAre;

namespace {

bool ContainsError(const ErrorContainer &errors,
                   ErrorDefinition::ErrorType etype) {
  return std::count_if(
      errors.getErrors().begin(), errors.getErrors().end(),
      [etype](const Error &e) { return e.getType() == etype; });
}

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
  assign c = `BAR(((4 * c)), ((3*d)));
endmodule)");

  EXPECT_EQ(res, R"(
module top();
  assign b = (3 * c)*2+( 2*d );
  assign c = (((4 * c)))*2+( ((3*d)) );
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

TEST(PreprocessTest, PreprocessMacroReportErrorOnTooManyParameters) {
  PreprocessHarness harness;
  const std::string res = harness.preprocess(R"(
`define FOO_FUN(a) a * 42
module top();
  assign a = `FOO_FUN(123, 12);
endmodule)");

  EXPECT_TRUE(ContainsError(harness.collected_errors(),
                            ErrorDefinition::PP_TOO_MANY_ARGS_MACRO));

  EXPECT_EQ(res, R"(
module top();
  assign a = 123 * 42;
endmodule)");
}

// With zero arg macro, the testing for too many args fails.
// Documenting a bug: this results in unexpected results.
TEST(PreprocessTest, PreprocessMacroReportErrorOnOneInsteadZeroParameters) {
  PreprocessHarness harness;
  const std::string res = harness.preprocess(R"(
`define FOO_FUN() 42
module top();
  assign a = `FOO_FUN(123);
endmodule)");

  EXPECT_TRUE(ContainsError(harness.collected_errors(),
                            ErrorDefinition::PP_TOO_MANY_ARGS_MACRO));
}

TEST(PreprocessTest, IfdefCodeSelectionIfBranch) {
  PreprocessHarness harness;
  const std::string res = harness.preprocess(R"(
`define FOO 1
module top();
`ifdef FOO
  assign a = 42;
`else
  assign a = 2;
`endif
endmodule)");

  // In the result it is interesting that the `define itself and the else area
  // is entirely removed and not even showing up as newline.
  // This could break line counting later in the pipeline.
  EXPECT_EQ(res, R"(
module top();

  assign a = 42;

endmodule)");
}

TEST(PreprocessTest, IfdefCodeSelectionElseBranch) {
  PreprocessHarness harness;
  const std::string res = harness.preprocess(R"(
`define BAR 1
module top();
`ifdef FOO
  assign a = 42;
`else
  assign a = 2;
`endif
endmodule)");

  // Similar observation w.r.t. missing newlines as in previous test.
  EXPECT_EQ(res, R"(
module top();

  assign a = 2;

endmodule)");
}

}  // namespace
}  // namespace SURELOG
