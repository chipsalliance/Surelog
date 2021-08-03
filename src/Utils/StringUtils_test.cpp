/*
 Copyright 2020 The Surelog Team.

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

#include "Utils/StringUtils.h"

#include <string>
#include <string_view>
#include <vector>

#include "gmock/gmock.h"
#include "gtest/gtest.h"

using ::testing::ElementsAre;

namespace SURELOG {
namespace {
TEST(StringUtilsTest, Tokenize) {
  std::vector<std::string> tok_result;
  StringUtils::tokenize("A;tokenized. string,List", ",.;", tok_result);
  EXPECT_EQ(tok_result.size(), size_t(4));
  EXPECT_THAT(tok_result, ElementsAre("A", "tokenized", " string", "List"));
}

TEST(StringUtilsTest, TokenizeMulti) {
  std::vector<std::string> tok_result;
  StringUtils::tokenizeMulti("Mary_¯Had_¯a_¯little_¯lamb", "_¯", tok_result);
  EXPECT_EQ(tok_result.size(), size_t(5));
  EXPECT_THAT(tok_result, ElementsAre("Mary", "Had", "a", "little", "lamb"));
}

TEST(StringUtilsTest, TokenizeBalanced) {
  std::vector<std::string> tok_result;
  StringUtils::tokenizeBalanced(
      "\"some text\" (that has) {multiple clusters} "
      "[that shall not break]",
      " ", tok_result);
  EXPECT_EQ(tok_result.size(), size_t(4));
  EXPECT_THAT(tok_result,
              ElementsAre("\"some text\"", "(that has)", "{multiple clusters}",
                          "[that shall not break]"));
}

// TODO: tests needed for replaceInTokenVector()

TEST(StringUtilsTest, GetFirstNonEmptyToken) {
  EXPECT_EQ("hello", StringUtils::getFirstNonEmptyToken({" ", " ", "hello"}));

  // Unlike the name implies, 'empty' actually doesn't mean empty, but
  // one space. The function needs to be renamed, here just documenting.
  EXPECT_NE("hello", StringUtils::getFirstNonEmptyToken({"", " ", "hello"}));
}

TEST(StringUtilsTest, InPlaceSpaceTrimming) {
  std::string str;

  str = " \thello world\t ";
  StringUtils::ltrim(str);
  EXPECT_EQ("hello world\t ", str);

  str = " \thello world\t ";
  StringUtils::rtrim(str);
  EXPECT_EQ(" \thello world", str);

  str = " \thello world\t ";
  StringUtils::trim(str);
  EXPECT_EQ("hello world", str);
}

TEST(StringUtilsTest, InPlaceEraseUntilChar) {
  std::string str;

  // Erase up to the character
  str = "abcdefg";
  StringUtils::ltrim(str, 'd');
  EXPECT_EQ("efg", str);

  str = "abcdefg";
  StringUtils::rtrim(str, 'd');
  EXPECT_EQ("abc", str);

  // No change if string not found
  str = "abcdefg";
  StringUtils::ltrim(str, 'x');
  EXPECT_EQ("abcdefg", str);

  str = "abcdefg";
  StringUtils::rtrim(str, 'x');
  EXPECT_EQ("abcdefg", str);
}

TEST(StringUtilsTest, InPlaceRtrimEqual) {
  std::string str = " this is some  =  assignment ";

  StringUtils::rtrimEqual(str);
  EXPECT_EQ(" this is some  ", str);
}

TEST(StringUtilsTest, Leaf) {
  EXPECT_EQ("baz", StringUtils::leaf("foo.bar.baz"));
  EXPECT_EQ("", StringUtils::leaf("foo.bar."));
  EXPECT_EQ("", StringUtils::leaf(""));
  EXPECT_EQ("foo", StringUtils::leaf(".foo"));
}

TEST(StringUtilsTest, ReplaceAll) {
  EXPECT_EQ("The String With Space",
            StringUtils::replaceAll("TheFOOStringFOOWithFOOSpace", "FOO", " "));

  // Various substring situations.
  EXPECT_EQ("xABCyABCzABC", StringUtils::replaceAll("xAyAzA", "A", "ABC"));
  EXPECT_EQ("xAyAzA", StringUtils::replaceAll("xABCyABCzABC", "ABC", "A"));

  // Empty string corner-case testing.
  EXPECT_EQ("", StringUtils::replaceAll("", "A", "B"));
  EXPECT_EQ("", StringUtils::replaceAll("A", "A", ""));
}

TEST(StringUtilsTest, GetLineInString) {
  constexpr std::string_view input_text = "one\ntwo\nthree\nno-newline";
  // Lines are one-indexed
  EXPECT_EQ("one\n", StringUtils::getLineInString(input_text, 1));
  EXPECT_EQ("two\n", StringUtils::getLineInString(input_text, 2));
  EXPECT_EQ("three\n", StringUtils::getLineInString(input_text, 3));
  // If bulk ends without newline, the line is still valid.
  EXPECT_EQ("no-newline", StringUtils::getLineInString(input_text, 4));

  // Out-of-range accesses.
  EXPECT_EQ("", StringUtils::getLineInString(input_text, 0));
  EXPECT_EQ("", StringUtils::getLineInString(input_text, 5));
}

TEST(StringUtilsTest, RemoveComments) {
  EXPECT_EQ("hello ", StringUtils::removeComments("hello // world"));
  EXPECT_EQ("hello ", StringUtils::removeComments("hello # world"));
  EXPECT_EQ("hello \nworld",
            StringUtils::removeComments("hello # world\nworld"));

#if 0
  // TODO: does not ignore comment-like characters in strings
  EXPECT_EQ("hello \"#\" world",
            StringUtils::removeComments("hello \"#\" world # comment"));
  EXPECT_EQ("hello \"//\" world",
            StringUtils::removeComments("hello \"//\" world // comment"));
#endif
}

TEST(StringUtilsTest, DoubleStringConversion) {
  EXPECT_EQ("3", StringUtils::to_string(3.1415926, 0));
  EXPECT_EQ("3.1", StringUtils::to_string(3.1415926, 1));

  // Proper rounding.
  EXPECT_EQ("2", StringUtils::to_string(1.99, 0));
  EXPECT_EQ("2.0", StringUtils::to_string(1.96, 1));
  EXPECT_EQ("1.9", StringUtils::to_string(1.94, 1));
}

TEST(StringUtilsTest, EvaluateEnvironmentVariables) {
  // Variables not set are expanded to an empty string.
  EXPECT_EQ("hello  bar",
            StringUtils::evaluateEnvVars("hello ${TESTING_UNKNOWN_VAR} bar"));
  EXPECT_EQ("hello  bar",
            StringUtils::evaluateEnvVars("hello $TESTING_UNKNOWN_VAR/ bar"));

  // Variables set via the environment
  setenv("TESTING_EVAL_FOO", "foo-value", 1);
  setenv("TESTING_EVAL_BAR", "bar-value", 1);

  EXPECT_EQ("hello foo-value bar",
            StringUtils::evaluateEnvVars("hello ${TESTING_EVAL_FOO} bar"));

#if defined(_MSC_VER) || defined(__MINGW32__) || defined(__CYGWIN__)
#define EXPECTED_SEPARATOR "\\"
#else
#define EXPECTED_SEPARATOR "/"
#endif

  EXPECT_EQ("hello bar-value" EXPECTED_SEPARATOR " bar",
            StringUtils::evaluateEnvVars("hello $TESTING_EVAL_BAR/ bar"));

  // Variables set via registerEnvVar()
  EXPECT_EQ("hello  bar",
            StringUtils::evaluateEnvVars("hello ${REGISTERED_EVAL_FOO} bar"));

  StringUtils::registerEnvVar("REGISTERED_EVAL_FOO", "foo-reg");
  EXPECT_EQ("hello foo-reg bar",
            StringUtils::evaluateEnvVars("hello ${REGISTERED_EVAL_FOO} bar"));
}

}  // namespace
}  // namespace SURELOG
