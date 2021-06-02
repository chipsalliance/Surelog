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
TEST(PreprocessTest, BasicPp) {
  PreprocessHarness harness;
  {
    std::string res = harness.preprocess("module top(); endmodule");
    EXPECT_EQ(res, "module top(); endmodule");
  }
  {
    std::string res = harness.preprocess(
        "`define FOO(a) a*2\n\n\
    module top();\n\
    assign b = `FOO(c);\n\
    endmodule");
    EXPECT_EQ(res,
              "\n\
    module top();\n\
    assign b = c*2;\n\
    endmodule");
  }
}
}  // namespace
}  // namespace SURELOG
