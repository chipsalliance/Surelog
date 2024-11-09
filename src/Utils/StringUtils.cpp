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
 * File:   StringUtils.cpp
 * Author: alain
 *
 * Created on March 14, 2017, 10:43 PM
 */

#include "Surelog/Utils/StringUtils.h"

#include <algorithm>
#include <array>
#include <cstdint>
#include <locale>
#include <map>
#include <regex>
#include <sstream>
#include <string>

namespace SURELOG {

static std::map<std::string, std::string> envVars;

std::string StringUtils::to_string(double a_value, const int32_t n) {
  std::ostringstream out;
  out.precision(n);
  out << std::fixed << a_value;
  return out.str();
}

std::vector<std::string_view>& StringUtils::tokenizeMulti(
    std::string_view str, std::string_view multichar_separator,
    std::vector<std::string_view>& result) {
  if (str.empty()) return result;

  size_t start = 0;
  size_t end = 0;
  const size_t sepSize = multichar_separator.size();
  const size_t stringSize = str.size();
  for (size_t i = 0; i < stringSize; i++) {
    bool isSeparator = true;
    for (size_t j = 0; j < sepSize; j++) {
      if (i + j >= stringSize) break;
      if (str[i + j] != multichar_separator[j]) {
        isSeparator = false;
        break;
      }
    }
    if (isSeparator) {
      result.emplace_back(str.data() + start, end - start);
      start = end = end + sepSize;
      i = i + sepSize - 1;
    } else {
      ++end;
    }
  }
  result.emplace_back(str.data() + start, end - start);
  return result;
}

std::vector<std::string>& StringUtils::tokenizeMulti(
    std::string_view str, std::string_view multichar_separator,
    std::vector<std::string>& result) {
  std::vector<std::string_view> view_result;
  tokenizeMulti(str, multichar_separator, view_result);
  result.insert(result.end(), view_result.begin(), view_result.end());
  return result;
}

std::vector<std::string_view>& StringUtils::tokenize(
    std::string_view str, std::string_view any_of_separators,
    std::vector<std::string_view>& result) {
  if (str.empty()) return result;

  std::array<bool, 256> separators = {false};
  for (char ch : any_of_separators) {
    separators[(int32_t)ch] = true;
  }

  size_t start = 0;
  size_t end = 0;
  for (char ch : str) {
    if (separators[(int32_t)ch]) {
      result.emplace_back(str.data() + start, end - start);
      end = start = end + 1;
    } else {
      ++end;
    }
  }
  result.emplace_back(str.data() + start, end - start);
  return result;
}

std::vector<std::string>& StringUtils::tokenize(
    std::string_view str, std::string_view any_of_separators,
    std::vector<std::string>& result) {
  std::vector<std::string_view> view_result;
  tokenize(str, any_of_separators, view_result);
  result.insert(result.end(), view_result.begin(), view_result.end());
  return result;
}

std::vector<std::string_view>& StringUtils::tokenizeBalanced(
    std::string_view str, std::string_view any_of_separators,
    std::vector<std::string_view>& result) {
  if (str.empty()) return result;

  std::array<bool, 256> separators = {false};
  for (char ch : any_of_separators) {
    separators[(int32_t)ch] = true;
  }

  const uint32_t stringSize = str.size();
  size_t start = 0;
  size_t end = 0;
  int32_t level = 0;
  bool inDoubleQuote = false;
  for (size_t i = 0; i < stringSize; i++) {
    if (str[i] == '"') {
      if (!inDoubleQuote) {
        level++;
        inDoubleQuote = true;
      } else {
        level--;
        inDoubleQuote = false;
      }
    } else if (str[i] == '(' || str[i] == '[' || str[i] == '{') {
      level++;
    } else if (str[i] == ')' || str[i] == ']' || str[i] == '}') {
      level--;
    }
    if ((level == 0) && separators[(int32_t)str[i]]) {
      result.emplace_back(str.data() + start, end - start);
      start = end = i + 1;
    } else {
      ++end;
    }
  }
  result.emplace_back(str.data() + start, end - start);
  return result;
}

// Remove line feed unless it is escaped with backslash.
static std::string removeLF(std::string_view st) {
  if (st.find('\n') == std::string::npos) return std::string(st);

  std::string result;
  char previous = '\0';
  for (const char c : st) {
    if (c != '\n' || previous == '\\') result += c;
    previous = c;
  }
  return result;
}

void StringUtils::replaceInTokenVector(
    std::vector<std::string>& tokens,
    const std::vector<std::string_view>& pattern, std::string_view news) {
  uint32_t patternIndex = 0;
  std::vector<std::string>::iterator itr;
  bool more = true;
  while (more) {
    more = false;
    for (itr = tokens.begin(); itr != tokens.end(); itr++) {
      if (patternIndex > 0 && *itr != pattern[patternIndex])
        patternIndex = 0;  // Restart
      if (*itr == pattern[patternIndex]) {
        patternIndex++;
        if (patternIndex == pattern.size()) {
          *itr = news;
          patternIndex = 0;
          itr = tokens.erase(itr - (pattern.size() - 1), itr);
          more = true;
        }
      }
    }
  }
}

void StringUtils::replaceInTokenVector(std::vector<std::string>& tokens,
                                       std::string_view pattern,
                                       std::string_view news) {
  const std::string news_s(news);
  uint32_t tokensSize = tokens.size();
  for (uint32_t i = 0; i < tokensSize; i++) {
    if (tokens[i] == pattern) {
      const bool surrounded_by_quotes =
          (i > 0 && (tokens[i - 1] == "\"")) &&
          ((i < tokensSize - 1) && (tokens[i + 1] == "\""));
      tokens[i] = surrounded_by_quotes ? removeLF(news) : news_s;
    }
  }
}

std::string_view StringUtils::ltrim(std::string_view str) {
  while (!str.empty() &&
         std::isspace<char>(str.front(), std::locale::classic())) {
    str.remove_prefix(1);
  }
  return str;
}

std::string_view StringUtils::rtrim(std::string_view str) {
  while (!str.empty() &&
         std::isspace<char>(str.back(), std::locale::classic())) {
    str.remove_suffix(1);
  }
  return str;
}

std::string_view StringUtils::trim(std::string_view str) {
  return ltrim(rtrim(str));
}

std::string_view StringUtils::rtrim_until(std::string_view str, char c) {
  auto pos = str.rfind(c);
  if (pos != std::string_view::npos) str = str.substr(0, pos);
  return str;
}

std::string_view StringUtils::ltrim_until(std::string_view str, char c) {
  auto pos = str.find(c);
  if (pos != std::string_view::npos) str = str.substr(pos + 1);
  return str;
}

std::string_view StringUtils::leaf(std::string_view str) {
  const auto found_dot = str.rfind('.');
  return found_dot == std::string_view::npos ? str : str.substr(found_dot + 1);
}

std::string StringUtils::replaceAll(std::string_view str, std::string_view from,
                                    std::string_view to) {
  size_t start_pos = 0;
  std::string result(str);
  while ((start_pos = result.find(from, start_pos)) != std::string::npos) {
    result.replace(start_pos, from.length(), to);
    start_pos += to.length();  // Handles case where 'to' is a substr of 'from'
  }
  return result;
}

// Split off the next view split with "separator" character.
// Modifies "src" to contain the remaining string.
// If "src" is exhausted, returned string-view will have data() == nullptr.
static std::string_view SplitNext(std::string_view* src, char separator) {
  if (src->empty()) return {nullptr, 0};  // Done.

  const auto pos = src->find(separator);
  const auto part_len = (pos != std::string_view::npos) ? pos + 1 : src->size();
  std::string_view result = src->substr(0, part_len);
  src->remove_prefix(part_len);
  return result;
}

std::string_view StringUtils::getLineInString(std::string_view text,
                                              int32_t line) {
  if (line < 1) return "";

  std::string_view s;
  while (line && (s = SplitNext(&text, '\n'), s.data()) != nullptr) {
    --line;
  }
  return s;
}

std::vector<std::string_view> StringUtils::splitLines(std::string_view text) {
  std::vector<std::string_view> result;
  std::string_view s;
  while ((s = SplitNext(&text, '\n'), s.data()) != nullptr) {
    result.emplace_back(s);
  }
  return result;
}

std::string StringUtils::removeComments(std::string_view text) {
  std::string result;
  char c1 = '\0';
  bool inComment = 0;
  for (char c2 : text) {
    if ((c2 == '/') && (c1 == '/') && !inComment) {
      inComment = true;
      result.erase(result.end() - 1);
    }
    if ((c1 == ' ' || c1 == '#' || c1 == '\0' || c1 == '\t' || c1 == '\n') &&
        c2 == '#')
      inComment = true;
    if (c2 == '\n') inComment = false;
    if (!inComment) result += c2;
    c1 = c2;
  }
  return result;
}

// Update the input string.

void StringUtils::autoExpandEnvironmentVariables(std::string* text) {
  static std::regex env(R"(\$\{([^}]+)\})");
  std::smatch match;
  while (std::regex_search(*text, match, env)) {
    std::string var;
    const char* s = getenv(match[1].str().c_str());
    if (s == nullptr) {
      auto itr = envVars.find(match[1].str());
      if (itr != envVars.end()) var = (*itr).second;
    }
    if (var.empty() && s) var = s;
    text->replace(match.position(0), match.length(0), var);
  }
  static std::regex env2("\\$([a-zA-Z0-9_]+)/");
  while (std::regex_search(*text, match, env2)) {
    std::string var;
    const char* s = getenv(match[1].str().c_str());
    if (s == nullptr) {
      auto itr = envVars.find(match[1].str());
      if (itr != envVars.end()) var = (*itr).second;
    }
    if (var.empty() && s) var = s;
#if defined(_MSC_VER) || defined(__MINGW32__) || defined(__CYGWIN__)
    if (!var.empty() && (var[var.size() - 1] != '\\')) var += "\\";
#else
    if (!var.empty() && (var[var.size() - 1] != '/')) var += "/";
#endif
    text->replace(match.position(0), match.length(0), var);
  }
  static std::regex env3(R"(\$\(([^}]+)\))");
  while (std::regex_search(*text, match, env3)) {
    std::string var;
    const char* s = getenv(match[1].str().c_str());
    if (s == nullptr) {
      auto itr = envVars.find(match[1].str());
      if (itr != envVars.end()) var = (*itr).second;
    }
    if (var.empty() && s) var = s;
    text->replace(match.position(0), match.length(0), var);
  }
}

// Leave input alone and return new string.
std::string StringUtils::evaluateEnvVars(std::string_view text) {
  std::string input(text.begin(), text.end());
  autoExpandEnvironmentVariables(&input);
  return input;
}

void StringUtils::registerEnvVar(std::string_view var, std::string_view value) {
  envVars.emplace(var, value);
}

std::string_view StringUtils::unquoted(std::string_view text) {
  if ((text.size() >= 2) &&
      (((text.front() == '\"') && (text.back() == '\"')) ||
       ((text.front() == '\'') && (text.back() == '\'')))) {
    text.remove_prefix(1);
    text.remove_suffix(1);
  }
  return text;
}

bool StringUtils::startsWith(std::string_view text, std::string_view prefix) {
  return (text.size() >= prefix.size()) &&
         (text.compare(0, prefix.size(), prefix) == 0);
}

bool StringUtils::endsWith(std::string_view text, std::string_view suffix) {
  return (text.size() >= suffix.size()) &&
         (text.compare(text.size() - suffix.size(), suffix.size(), suffix) ==
          0);
}
}  // namespace SURELOG
