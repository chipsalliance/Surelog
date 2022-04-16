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
#include <Surelog/DesignCompile/CompileHelper.h>
#include <gmock/gmock.h>
#include <gtest/gtest.h>
#include <uhdm/Serializer.h>
#include <uhdm/constant.h>

#include <limits>

namespace SURELOG {

TEST(CompileHelper, ParseConstants) {
  UHDM::Serializer s;
  auto tester = [&s](int type, const std::string& value, int64_t* result) {
    CompileHelper testee;
    UHDM::constant* val = s.MakeConstant();
    val->VpiConstType(type);
    val->VpiValue(value);
    return testee.parseConstant(*val, result);
  };

  int64_t result;
  {  // Binary
    EXPECT_TRUE(tester(vpiBinaryConst, "BIN:1010", &result));
    EXPECT_EQ(result, 0b1010);

    EXPECT_TRUE(tester(vpiBinaryConst, "BIN:" + std::string(63, '1'), &result));
    EXPECT_EQ((uint64_t)result, 0x7FFFFFFFFFFFFFFFuLL);

    EXPECT_TRUE(tester(vpiBinaryConst, "BIN:" + std::string(64, '1'), &result));
    EXPECT_EQ((uint64_t)result, 0xFFFFFFFFFFFFFFFFuLL);

    // Out of range.
    EXPECT_FALSE(
        tester(vpiBinaryConst, "BIN:" + std::string(65, '1'), &result));
  }

  {  // Decimal tests

    EXPECT_TRUE(tester(vpiDecConst, "DEC:42", &result));
    EXPECT_EQ(result, 42);

    EXPECT_TRUE(tester(vpiDecConst, "DEC:-42", &result));
    EXPECT_EQ(result, -42);

    // Decimal is signed, so we expect overrflow using more than 63 bits.
    EXPECT_TRUE(tester(vpiDecConst, "DEC:9223372036854775807", &result));
    EXPECT_EQ(result, std::numeric_limits<int64_t>::max());

    // Positive Out of range
    EXPECT_FALSE(tester(vpiDecConst, "DEC:9223372036854775808", &result));

    EXPECT_TRUE(tester(vpiDecConst, "DEC:-9223372036854775808", &result));
    EXPECT_EQ(result, std::numeric_limits<int64_t>::min());

    // Negative Out of range
    EXPECT_FALSE(tester(vpiDecConst, "DEC:-9223372036854775809", &result));
  }

  {  // Integer tests. Essentially same as decimal
    EXPECT_TRUE(tester(vpiIntConst, "INT:42", &result));
    EXPECT_EQ(result, 42);

    EXPECT_TRUE(tester(vpiIntConst, "INT:-42", &result));
    EXPECT_EQ(result, -42);

    // Decimal is signed, so we expect overrflow using more than 63 bits.
    EXPECT_TRUE(tester(vpiIntConst, "INT:9223372036854775807", &result));
    EXPECT_EQ(result, std::numeric_limits<int64_t>::max());

    // Positive Out of range
    EXPECT_FALSE(tester(vpiIntConst, "INT:9223372036854775808", &result));

    EXPECT_TRUE(tester(vpiIntConst, "INT:-9223372036854775808", &result));
    EXPECT_EQ(result, std::numeric_limits<int64_t>::min());

    // Negative Out of range
    EXPECT_FALSE(tester(vpiIntConst, "INT:-9223372036854775809", &result));
  }

  {  // Unsigned
    EXPECT_TRUE(tester(vpiUIntConst, "UINT:18446744073709551615", &result));
    EXPECT_EQ((uint64_t)result, 18446744073709551615uLL);

    // Out of range.
    EXPECT_FALSE(tester(vpiUIntConst, "UINT:18446744073709551616", &result));

    // Negative values are allowed and interpreted as 2's complement, then
    // interpreted as unsigned.
    EXPECT_TRUE(tester(vpiUIntConst, "UINT:-1", &result));
    EXPECT_EQ((uint64_t)result, std::numeric_limits<uint64_t>::max());
  }

  {  // Hex
    EXPECT_TRUE(tester(vpiHexConst, "HEX:FF", &result));
    EXPECT_EQ(result, 0xFF);

    EXPECT_TRUE(tester(vpiHexConst, "HEX:FFFFFFFFFFFFFFFF", &result));
    EXPECT_EQ((uint64_t)result, std::numeric_limits<uint64_t>::max());
  }

  {  // Octal
    EXPECT_TRUE(tester(vpiOctConst, "OCT:377", &result));
    EXPECT_EQ(result, 0xff);

    EXPECT_TRUE(tester(vpiOctConst, "OCT:1777777777777777777777", &result));
    EXPECT_EQ((uint64_t)result, std::numeric_limits<uint64_t>::max());

    // Out of range.
    EXPECT_FALSE(tester(vpiOctConst, "OCT:3777777777777777777777", &result));
  }

  {                                                    // Broken input rejection
    EXPECT_FALSE(tester(vpiHexConst, "FF", &result));  // Prefix missing

    // Implementation limitation: the actual prefix is actually not tested,
    // so this is still valid.
    EXPECT_TRUE(tester(vpiHexConst, "ABC:FF", &result));
  }
}
}  // namespace SURELOG
