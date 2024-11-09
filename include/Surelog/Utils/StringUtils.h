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
 * File:   StringUtils.h
 * Author: alain
 *
 * Created on March 14, 2017, 10:43 PM
 */

#ifndef SURELOG_STRINGUTILS_H
#define SURELOG_STRINGUTILS_H
#pragma once

#include <sstream>
#include <string>
#include <string_view>
#include <vector>

namespace SURELOG {

// StrCat() and StrAppend() are fairly efficient (at least as good as +/+=)
// but more optimal implementations are possible (see absl::StrCat()
// absl::StrAppend(). So these are in the name and spirit of the absl version
// while being the simplest possible for now until optimization is needed.

// StrCat(): concatenate the string representations of each argument into
// a string which is returned.
template <typename... Ts>
std::string StrCat(Ts&&... args) {
  std::ostringstream out;
  (out << ... << std::forward<Ts>(args));
  return out.str();
}

// Similar to StrCat(), append arguments, converted to strings to "dest"
// string.
template <typename... Ts>
void StrAppend(std::string* dest, Ts&&... args) {
  std::ostringstream out;
  out << *dest;
  (out << ... << std::forward<Ts>(args));
  *dest = out.str();
}

namespace StringUtils {
// Tokenize "str" at "any_of_separator", store in "result" array.
std::vector<std::string_view>& tokenize(std::string_view str,
                                        std::string_view any_of_separators,
                                        std::vector<std::string_view>& result);
std::vector<std::string>& tokenize(std::string_view str,
                                   std::string_view any_of_separators,
                                   std::vector<std::string>& result);

// Tokenize "str" at "multichar_separator"; store in "result" array.
std::vector<std::string_view>& tokenizeMulti(
    std::string_view str, std::string_view multichar_separator,
    std::vector<std::string_view>& result);
std::vector<std::string>& tokenizeMulti(std::string_view str,
                                        std::string_view multichar_separator,
                                        std::vector<std::string>& result);

// Tokenizes "str" at "separator", but leaves 'bracketed' areas
// intact: "double quoted" (parenthesized) [foo] {bar}
std::vector<std::string_view>& tokenizeBalanced(
    std::string_view str, std::string_view any_of_separators,
    std::vector<std::string_view>& result);

// In "token" array, replace sequence of tokens that match "pattern" with
// a single element "news"
void replaceInTokenVector(std::vector<std::string>& tokens,
                          const std::vector<std::string_view>& pattern,
                          std::string_view news);

// Replace every item in "tokens" that matches "pattern" with "news".
//
// Including surprising feature: if the pattern is just between
// double-quotes right and left in the tokens-array, carriage return is
// removed in "news". TODO: less surprises.
void replaceInTokenVector(std::vector<std::string>& tokens,
                          std::string_view pattern, std::string_view news);

// Remove whitespace at the beginning of the string.
[[nodiscard]] std::string_view ltrim(std::string_view str);

// Remove whitespace at the end of the string.
[[nodiscard]] std::string_view rtrim(std::string_view str);

// Removing spaces on both ends.
[[nodiscard]] std::string_view trim(std::string_view str);

// Erase left of the string until given character is reached.
// Erases the input character as well.
[[nodiscard]] std::string_view ltrim_until(std::string_view str, char c);

// Erase right of the string until given character is reached.
// Erases the input character as well.
[[nodiscard]] std::string_view rtrim_until(std::string_view str, char c);

// Return the last element of a dot-separated path foo.bar.baz -> baz
[[nodiscard]] std::string_view leaf(std::string_view str);

// In given string "str", replace all occurences of "from" with "to"
std::string replaceAll(std::string_view str, std::string_view from,
                       std::string_view to);

// Given a large input, return the content of line number "line".
// Lines are 1 indexed. The newline separator is included in the
// returned lines; the last line in text might not have a newline
// so will not be included.
[[nodiscard]] std::string_view getLineInString(std::string_view text,
                                               int32_t line);

// Split input text into lines at '\n'. This separator is included in the
// returned lines; the last line in text might not have a newline so will
// not be included.
std::vector<std::string_view> splitLines(std::string_view text);

// Convert double number with given amount of precision.
std::string to_string(double a_value, int32_t n = 3);

// Remove '//' and '#'-style end-of-line comments
[[nodiscard]] std::string removeComments(std::string_view text);

// Expand environment variables in the form of ${FOO} or $FOO/
// (variable followed by slash) in string. Modifies the string.
void autoExpandEnvironmentVariables(std::string* text);

// Like autoExpandEnvironmentVariables(), but returns modified string.
std::string evaluateEnvVars(std::string_view text);

void registerEnvVar(std::string_view var, std::string_view value);

// Strip quotes, if any. "abc" => abc
[[nodiscard]] std::string_view unquoted(std::string_view text);

// Returns true if string 'text' starts with 'prefix'
[[nodiscard]] bool startsWith(std::string_view text, std::string_view prefix);

// Returns true if string 'text' ends with 'suffix'
[[nodiscard]] bool endsWith(std::string_view text, std::string_view suffix);
}  // namespace StringUtils
}  // namespace SURELOG

#endif /* SURELOG_STRINGUTILS_H */
