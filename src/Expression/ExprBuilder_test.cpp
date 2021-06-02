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

#include "Expression/ExprBuilder.h"

#include <string>
#include <string_view>
#include <vector>

#include "gmock/gmock.h"
#include "gtest/gtest.h"

using ::testing::ElementsAre;

namespace SURELOG {
namespace {
TEST(ExprBuilderTest, BasicValueOp) {
  {
    LValue v0, v1, v2;
    v1.set((int64_t)1);
    v2.set((int64_t)0);
    v0.bitwAnd(&v1, &v2);
    EXPECT_EQ(v0.getValueL(), 0);
  }

  {
    LValue v0, v1, v2;
    v1.set((int64_t)1);
    v2.set((int64_t)0);
    v0.bitwOr(&v1, &v2);
    EXPECT_EQ(v0.getValueL(), 1);
  }
  {
    LValue v0, v1;
    v1.set((int64_t)1);
    v0.u_not(&v1);
    EXPECT_EQ(v0.getValueL(), 0);
  }
  {
    LValue v0, v1, v2;
    v1.set((int64_t)-1);
    v2.set((int64_t)1);
    v0.plus(&v1, &v2);
    EXPECT_EQ(v0.getValueL(), 0);
  }
  {
    LValue v0, v1, v2;
    v1.set((int64_t)-10);
    v2.set((int64_t)9);
    v0.plus(&v1, &v2);
    EXPECT_EQ(v0.getValueL(), -1);
    EXPECT_EQ(v0.uhdmValue(), "INT:-1");
  }
  {
    ValueFactory factory;
    Value* v0 = factory.newStValue();
    v0->set("BLAH");
    EXPECT_EQ(v0->uhdmValue(), "STRING:BLAH");
  }
}
TEST(ExprBuilderTest, BuildFrom) {
  {
    ExprBuilder builder;
    Value* v1 = builder.fromVpiValue("HEX:A");
    Value* v2 = builder.fromVpiValue("INT:10");
    Value* v3 = builder.fromString("2'b11");
    Value* v4 = builder.fromString("4'hFF_FF");
    Value* v5 = builder.fromString("-0.6");
    Value* v6 = builder.fromVpiValue("UINT:11");
    LValue v0;
    v0.equiv(v1, v2);
    EXPECT_EQ(v1->uhdmValue(), "UINT:10");
    EXPECT_EQ(v0.getValueL(), 1);
    EXPECT_EQ(v3->getValueL(), 3);
    EXPECT_EQ(v4->uhdmValue(), "HEX:FFFF");
    EXPECT_EQ(v5->getValueD(), -0.6);
    EXPECT_EQ(v6->uhdmValue(), "UINT:11");
  }
}
}  // namespace
}  // namespace SURELOG
