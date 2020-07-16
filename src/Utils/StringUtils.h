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

#ifndef STRINGUTILS_H
#define STRINGUTILS_H

#include <map>
#include <string>
#include <string_view>
#include <vector>

namespace SURELOG {

class StringUtils {
 public:
  // Tokenize "str" at "any_of_separator", store in "result" array.
  static void tokenize(std::string_view str,
                       std::string_view any_of_separator,
                       std::vector<std::string>& result);

  // Tokenize "str" at "multichar_separator"; store in "result" array.
  static void tokenizeMulti(std::string_view str,
                            std::string_view multichar_separator,
                            std::vector<std::string>& result);

  // Tokenizes "str" at "separator", but leaves 'bracketed' areas
  // intact: "double quoted" (parenthesized) [foo] {bar}
  static void tokenizeBalanced(std::string_view str,
                               std::string_view separator,
                               std::vector<std::string>& result);
  static void replaceInTokenVector(std::vector<std::string>& tokens,
                                   std::vector<std::string> pattern,
                                   std::string_view news);
  static void replaceInTokenVector(std::vector<std::string>& tokens,
                                   std::string_view pattern,
                                   std::string_view news);

  // Given a list of tokens, return the first that is not a single space.
  // (unlike the name implies, it does not look for empty but space. TODO
  //  rename)
  static std::string getFirstNonEmptyToken(
    const std::vector<std::string>& tokens);

  // TODO: these should not modify strings, but rather return trimmed
  // std::string_views.

  // Modify string string, remove whitespace at the beginning of the string.
  static std::string& ltrim(std::string& str);

  // Modify string string, remove whitespace at the end of the string.
  static std::string& rtrim(std::string& str);

  // Modify string, removing spaces on both ends.
  static std::string& trim(std::string& str);

  // Erase left of the string until given character is reached. If this
  // is not reached, the string is unchanged. Modifies string.
  // TODO: this name is confusing, as it does not do the same as the other
  // trim functions (which trim characters until there is none)
  static std::string& ltrim(std::string& str, char c);

  // Erase right of the string until given character is reached. If this
  // is not reached, the string is unchanged. Modifies string.
  // TODO: this name is confusing, as it does not do the same as the other
  // trim functions (which trim characters until there is none)
  static std::string& rtrim(std::string& str, char c);

  // Trim and modify string at assignment character.
  static std::string& rtrimEqual(std::string& str);

  // Return the last element of a dot-separated path foo.bar.baz -> baz
  static std::string leaf(std::string str);

  // In given string "str", replace all occurences of "from" with "to"
  static std::string replaceAll(std::string_view str,
                                std::string_view from,
                                std::string_view to);

  // Given a large input, return the content of line number "line". Lines
  // are 1 indexed.
  static std::string getLineInString(std::string_view bulk, unsigned int line);

  // Convert double number with given amount of precision.
  static std::string to_string(double a_value, const int n = 3);

  static std::string removeComments(std::string_view text);

  static std::string evaluateEnvVars(std::string_view text);
  static void autoExpandEnvironmentVariables( std::string & text );
  static void registerEnvVar(std::string var, std::string value) {
      envVars.insert(std::make_pair(var, value));
  }

 private:
  StringUtils() = delete;
  StringUtils(const StringUtils& orig) = delete;
  ~StringUtils() = delete;

  static std::map<std::string, std::string> envVars;

 private:
};

};  // namespace SURELOG

#endif /* STRINGUTILS_H */
