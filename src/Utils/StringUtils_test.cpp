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

#include <Surelog/Utils/StringUtils.h>
#include <gmock/gmock.h>
#include <gtest/gtest.h>

namespace SURELOG {
using ::testing::ElementsAre;

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

TEST(StringUtilsTest, ReplaceInTokenVectorWithVectorPattern) {
  std::vector<std::string> tokens = {"c", "a", "b", "c", "x", "y"};

  // No pattern match
  StringUtils::replaceInTokenVector(tokens, {"a", "x"}, "foo");
  EXPECT_THAT(tokens, ElementsAre("c", "a", "b", "c", "x", "y"));

  // Pattern match
  StringUtils::replaceInTokenVector(tokens, {"a", "b", "c"}, "bar");
  EXPECT_THAT(tokens, ElementsAre("c", "bar", "x", "y"));

  // Pattern starts multiple times, but only full pattern counts
  tokens = {"a", "a", "b", "c", "x", "y"};
  StringUtils::replaceInTokenVector(tokens, {"a", "b", "c"}, "baz");
  EXPECT_THAT(tokens, ElementsAre("a", "baz", "x", "y"));

  tokens = {"a", "b", "a", "b", "c", "x", "y"};
  StringUtils::replaceInTokenVector(tokens, {"a", "b", "c"}, "quuz");
  EXPECT_THAT(tokens, ElementsAre("a", "b", "quuz", "x", "y"));
}

TEST(StringUtilsTest, ReplaceInTokenVectorWithVectorString) {
  std::vector<std::string> tokens = {"a", "b", "c"};

  // No pattern match
  StringUtils::replaceInTokenVector(tokens, "x", "foo");
  EXPECT_THAT(tokens, ElementsAre("a", "b", "c"));

  // Pattern match
  StringUtils::replaceInTokenVector(tokens, "b", "bar");
  EXPECT_THAT(tokens, ElementsAre("a", "bar", "c"));

  // Pattern match with tokens that are double-quotes
  tokens = {"\"", "b", "\""};
  StringUtils::replaceInTokenVector(tokens, "b", "baz");
  EXPECT_THAT(tokens, ElementsAre("\"", "baz", "\""));

  // Pattern match with newline replacement
  tokens = {"a", "b", "c"};
  StringUtils::replaceInTokenVector(tokens, "b", "bar\nbaz");
  EXPECT_THAT(tokens, ElementsAre("a", "bar\nbaz", "c"));

  // Pattern match with newline replacement between double-quote tokens
  // (surprising feature: replace newline)
  tokens = {"\"", "b", "\""};
  StringUtils::replaceInTokenVector(tokens, "b", "bar\nbaz");
  EXPECT_THAT(tokens, ElementsAre("\"", "barbaz", "\""));

  // Newlines are only replaced if they are not escaped with backslash
  tokens = {"\"", "b", "\""};
  StringUtils::replaceInTokenVector(tokens, "b", "bar\\\nbaz");
  EXPECT_THAT(tokens, ElementsAre("\"", "bar\\\nbaz", "\""));
}

TEST(StringUtilsTest, GetFirstNonEmptyToken) {
  EXPECT_EQ("hello", StringUtils::getFirstNonEmptyToken({" ", " ", "hello"}));

  // If all tokens are 'empty' (i.e. single space), returns actual empty string.
  EXPECT_EQ("", StringUtils::getFirstNonEmptyToken({" ", " ", " "}));

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
  EXPECT_EQ(StringUtils::leaf("foo.bar.baz"), "baz");
  EXPECT_EQ(StringUtils::leaf("foo.bar."), "");
  EXPECT_EQ(StringUtils::leaf(""), "");
  EXPECT_EQ(StringUtils::leaf(".foo"), "foo");
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
#if defined(_MSC_VER)
  _putenv_s("TESTING_EVAL_FOO", "foo-value");
  _putenv_s("TESTING_EVAL_BAR", "bar-value");
#else
  setenv("TESTING_EVAL_FOO", "foo-value", 1);
  setenv("TESTING_EVAL_BAR", "bar-value", 1);
#endif

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

TEST(StringUtilsTest, StrCat) {
  EXPECT_EQ("hello world", StrCat("hello ", "world"));  // const char*
  EXPECT_EQ("Answer 42", StrCat("Answer ", 42));        // Integer

  // String view.
  const std::string str_concat = "string";
  const std::string_view str_view_concat = "string_view";
  EXPECT_EQ("string string_view", StrCat(str_concat, " ", str_view_concat));
}

TEST(StringUtilsTest, StrAppend) {
  std::string target("Base string ");
  StrAppend(&target, "hello ", "world ", 42);
  EXPECT_EQ("Base string hello world 42", target);
}

}  // namespace
}  // namespace SURELOG
