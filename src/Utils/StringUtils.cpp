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

#include <Surelog/Utils/StringUtils.h>

#include <algorithm>
#include <iostream>
#include <locale>
#include <regex>
#include <sstream>

namespace SURELOG {

std::map<std::string, std::string> StringUtils::envVars;

std::string StringUtils::to_string(double a_value, const int n) {
  std::ostringstream out;
  out.precision(n);
  out << std::fixed << a_value;
  return out.str();
}

void StringUtils::tokenizeMulti(std::string_view str,
                                std::string_view separator,
                                std::vector<std::string>& result) {
  std::string tmp;
  const unsigned int sepSize = separator.size();
  const unsigned int stringSize = str.size();
  for (unsigned int i = 0; i < stringSize; i++) {
    bool isSeparator = true;
    for (unsigned int j = 0; j < sepSize; j++) {
      if (i + j >= stringSize) break;
      if (str[i + j] != separator[j]) {
        isSeparator = false;
        break;
      }
    }
    if (isSeparator) {
      i = i + sepSize - 1;
      result.push_back(tmp);
      tmp = "";
      if (i == (str.size() - 1)) result.push_back(tmp);
    } else if (i == (str.size() - 1)) {
      tmp += str[i];
      result.push_back(tmp);
      tmp = "";
    } else {
      tmp += str[i];
    }
  }
}

void StringUtils::tokenize(std::string_view str, std::string_view separator,
                           std::vector<std::string>& result) {
  std::string tmp;
  const unsigned int sepSize = separator.size();
  const unsigned int stringSize = str.size();
  for (unsigned int i = 0; i < stringSize; i++) {
    bool isSeparator = false;
    for (unsigned int j = 0; j < sepSize; j++) {
      if (str[i] == separator[j]) {
        isSeparator = true;
        break;
      }
    }
    if (isSeparator) {
      result.push_back(tmp);
      tmp = "";
      if (i == (str.size() - 1)) result.push_back(tmp);
    } else if (i == (str.size() - 1)) {
      tmp += str[i];
      result.push_back(tmp);
      tmp = "";
    } else {
      tmp += str[i];
    }
  }
}

void StringUtils::tokenizeBalanced(std::string_view str,
                                   std::string_view separator,
                                   std::vector<std::string>& result) {
  std::string tmp;
  const unsigned int sepSize = separator.size();
  const unsigned int stringSize = str.size();
  int level = 0;
  bool inDoubleQuote = false;
  for (unsigned int i = 0; i < stringSize; i++) {
    if (str[i] == '"') {
      if (!inDoubleQuote) {
        level++;
        inDoubleQuote = true;
      } else {
        level--;
        inDoubleQuote = false;
      }
    }
    if (str[i] == '(' || str[i] == '[' || str[i] == '{') {
      level++;
    }
    if (str[i] == ')' || str[i] == ']' || str[i] == '}') {
      level--;
    }
    bool isSeparator = false;
    for (unsigned int j = 0; j < sepSize; j++) {
      if (str[i] == separator[j]) {
        if (level == 0) isSeparator = true;
        break;
      }
    }
    if (isSeparator) {
      result.push_back(tmp);
      tmp = "";
      if (i == (str.size() - 1)) result.push_back(tmp);
    } else if (i == (str.size() - 1)) {
      tmp += str[i];
      result.push_back(tmp);
      tmp = "";
    } else {
      tmp += str[i];
    }
  }
}

// Remove carriage return unless it is escaped with backslash.
static std::string removeCR(std::string_view st) {
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
  unsigned int patternIndex = 0;
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
  unsigned int tokensSize = tokens.size();
  for (unsigned int i = 0; i < tokensSize; i++) {
    if (tokens[i] == pattern) {
      const bool surrounded_by_quotes =
          (i > 0 && (tokens[i - 1] == "\"")) &&
          ((i < tokensSize - 1) && (tokens[i + 1] == "\""));
      tokens[i] = surrounded_by_quotes ? removeCR(news) : news;
    }
  }
}

std::string StringUtils::getFirstNonEmptyToken(
    const std::vector<std::string>& tokens) {
  unsigned int tokensSize = tokens.size();
  for (unsigned int i = 0; i < tokensSize; i++) {
    if (tokens[i] != " ") return tokens[i];
  }
  return "";
}

std::string& StringUtils::trim(std::string& str) { return ltrim(rtrim(str)); }

std::string& StringUtils::ltrim(std::string& str) {
  auto it2 = std::find_if(str.begin(), str.end(), [](char ch) {
    return !std::isspace<char>(ch, std::locale::classic());
  });
  str.erase(str.begin(), it2);
  return str;
}

std::string& StringUtils::rtrim(std::string& str) {
  auto it1 = std::find_if(str.rbegin(), str.rend(), [](char ch) {
    return !std::isspace<char>(ch, std::locale::classic());
  });
  str.erase(it1.base(), str.end());
  return str;
}

std::string& StringUtils::rtrimEqual(std::string& str) {
  auto it1 = std::find_if(str.rbegin(), str.rend(),
                          [](char ch) { return (ch == '='); });
  if (it1 != str.rend()) str.erase(it1.base() - 1, str.end());
  return str;
}

std::string& StringUtils::rtrim(std::string& str, char c) {
  auto it1 = std::find_if(str.rbegin(), str.rend(),
                          [c](char ch) { return (ch == c); });
  if (it1 != str.rend()) str.erase(it1.base() - 1, str.end());
  return str;
}

std::string& StringUtils::ltrim(std::string& str, char c) {
  auto it1 =
      std::find_if(str.begin(), str.end(), [c](char ch) { return (ch == c); });
  if (it1 != str.end()) str.erase(str.begin(), it1 + 1);
  return str;
}

std::string_view StringUtils::leaf(std::string_view str) {
  const auto found_dot = str.find_last_of('.');
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

// TODO: have this return std::string_view to avoid copying the string,
// but first we need a unit test.
std::string StringUtils::getLineInString(std::string_view bulk,
                                         unsigned int line) {
  if (line < 1) return "";

  std::stringstream strm;
  strm << bulk;

  std::string lineText;
  while ((line > 0) && std::getline(strm, lineText, '\n')) {
    --line;
  }

  if ((line == 0) && strm.good()) lineText += '\n';
  if (line > 0) lineText.clear();
  return lineText;
}

std::string StringUtils::removeComments(std::string_view text) {
  std::string result;
  char c1 = '\0';
  bool inComment = 0;
  for (char c2 : text) {
     if ((c2 == '/') && (c1 == '/')) {
      inComment = true;
      result.erase(result.end() - 1);
    }
    if ((c1 == ' ' || c1 == '\0' || c1 == '\t') && c2 == '#') inComment = true;
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

std::string StringUtils::unquoted(const std::string& text) {
  if ((text.size() >= 2) && (text.front() == '\"') && (text.back() == '\"')) {
    return text.substr(1, text.length() - 2);
  }
  return text;
}

}  // namespace SURELOG
