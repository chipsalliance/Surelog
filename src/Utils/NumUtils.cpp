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
 * File:   NumUtils.cpp
 * Author: alain
 *
 * Created on December 29, 2020, 10:43 PM
 */

#include <Surelog/Utils/NumUtils.h>
#include <string.h>

#include <algorithm>
#include <bitset>
#include <iostream>
#include <locale>
#include <regex>
#include <sstream>

namespace SURELOG {

std::string NumUtils::hexToBin(const std::string &s) {
  std::string out;
  for (auto i : s) {
    uint8_t n;
    if ((i <= '9') && (i >= '0'))
      n = i - '0';
    else
      n = 10 + i - 'A';
    for (int8_t j = 3; j >= 0; --j) out.push_back((n & (1 << j)) ? '1' : '0');
  }
  out = trimLeadingZeros(out);
  return out;
}

std::string NumUtils::binToHex(const std::string &s) {
  std::string out;
  for (unsigned int i = 0; i < s.size(); i += 4) {
    int8_t n = 0;
    for (unsigned int j = i; j < i + 4; ++j) {
      n <<= 1;
      if (s[j] == '1') n |= 1;
    }

    if (n <= 9)
      out.push_back('0' + n);
    else
      out.push_back('A' + n - 10);
  }
  return out;
}

std::string NumUtils::toBinary(int size, uint64_t val) {
  int constexpr bitFieldSize = 100;
  std::string tmp = std::bitset<bitFieldSize>(val).to_string();
  if (size <= 0) {
    for (unsigned int i = 0; i < bitFieldSize; i++) {
      if (tmp[i] == '1') {
        size = bitFieldSize - i;
        break;
      }
    }
  }
  std::string result;
  for (unsigned int i = bitFieldSize - size; i < bitFieldSize; i++)
    result += tmp[i];
  return result;
}

std::string NumUtils::trimLeadingZeros(const std::string &s) {
  const uint64_t sSize = s.size();
  std::string res;
  bool nonZero = false;
  for (unsigned int i = 0; i < sSize; i++) {
    const char c = s[i];
    if (c != '0') nonZero = true;
    if (nonZero) res += c;
  }
  return res;
}

uint64_t NumUtils::getMask(uint64_t wide) {
  uint64_t mask = 0;
  uint64_t sizeInBits = sizeof(mask) * 8;
  mask = (wide >= sizeInBits)
             ? ((uint64_t)-1)
             : ((uint64_t)((uint64_t)(((uint64_t)1) << ((uint64_t)wide))) -
                (uint64_t)1);
  return mask;
}

/*
 * So, unfortunately not all c++17 implemenetations actually provide
 * a std::from_chars() for floating point numbers; available only >= g++-11
 * for instance.
 *
 * So here we use the c++ detection pattern to determine if that function
 * is available, otherwise fall back to slower best-effort implementation that
 * copies it to a nul-terminated buffer, then calls the old strtof(), strotd()
 * functions.
 */
template <typename T, typename = void>
struct from_chars_available : std::false_type {};
template <typename T>
struct from_chars_available<
    T, std::void_t<decltype(std::from_chars(
           std::declval<const char *>(), std::declval<const char *>(),
           std::declval<T &>()))>> : std::true_type {};

template <typename T>
inline constexpr bool from_chars_available_v = from_chars_available<T>::value;

// Copy everything that looks like a number into output iterator.
static void CopyNumberTo(const char *in_begin, const char *in_end,
                         char *out_begin, const char *out_end) {
  const char *src = in_begin;
  char *dst = out_begin;
  const char *extra_allowed = "+-.e";
  bool have_point = false;
  out_end -= 1;  // Allow space for 0 termination.
  while (src < in_end && (isdigit(*src) || strchr(extra_allowed, *src)) &&
         dst < out_end) {
    // The sign is only allowed in the first character of the buffer
    if ((*src == '+' || *src == '-') && dst != out_begin) break;
    // only allow one decimal point
    if (*src == '.') {
      if (have_point)
        break;
      else
        have_point = true;
    }
    *dst++ = *src++;
  }
  *dst = '\0';
}

template <typename T, T (*strto_fallback_fun)(const char *, char **)>
static const char *strto_ieee(std::string_view s, T *result) {
  if constexpr (from_chars_available_v<T>) {
    return internal::strto_num<T>(s, result);
  }

  // Fallback in case std::from_chars() does not exist for this type. Here,
  // we just call the corresponding C-function, but first have to copy
  // the number to a local buffer, as that one requires \0-termination.
  char buffer[64];

  // Need to skip whitespace first to not use up our buffer for that.
  std::string_view n = s;
  while (!n.empty() && isspace(n.front())) n.remove_prefix(1);

  CopyNumberTo(n.data(), n.data() + n.size(), buffer, buffer + sizeof(buffer));
  char *endptr = nullptr;
  *result = strto_fallback_fun(buffer, &endptr);
  if (endptr == buffer) return nullptr;  // Error.

  // Now, convert our offset back relative to the original string.
  return n.data() + (endptr - buffer);
}

const char *parse_float(std::string_view s, float *result) {
  return strto_ieee<float, strtof>(s, result);
}

const char *parse_double(std::string_view s, double *result) {
  return strto_ieee<double, strtod>(s, result);
}

const char *parse_longdouble(std::string_view s, long double *result) {
  return strto_ieee<long double, strtold>(s, result);
}

}  // namespace SURELOG
