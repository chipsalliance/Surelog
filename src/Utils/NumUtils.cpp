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

#include "Surelog/Utils/NumUtils.h"

#include <bitset>
#include <cstring>
#include <string>

namespace SURELOG {

std::string NumUtils::hexToBin(std::string_view s) {
  std::string out;
  out.reserve(s.length() * 4);
  for (auto i : s) {
    uint8_t n;
    if ((i <= '9') && (i >= '0'))
      n = i - '0';
    else
      n = 10 + i - 'A';
    for (int8_t j = 3; j >= 0; --j) out.push_back((n & (1 << j)) ? '1' : '0');
  }
  size_t pos = out.find('1');
  if (pos == std::string::npos)
    out.clear();
  else
    out = out.substr(pos);
  return out;
}

std::string NumUtils::binToHex(std::string_view s) {
  std::string out;
  out.reserve((s.length() + 3) / 4);
  for (uint32_t i = 0; i < s.size(); i += 4) {
    int8_t n = 0;
    for (uint32_t j = i; j < i + 4; ++j) {
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

std::string NumUtils::toBinary(int32_t size, uint64_t val) {
  int32_t constexpr bitFieldSize = 100;
  std::string tmp = std::bitset<bitFieldSize>(val).to_string();
  if (size <= 0) {
    for (uint32_t i = 0; i < bitFieldSize; i++) {
      if (tmp[i] == '1') {
        size = bitFieldSize - i;
        break;
      }
    }
  }
  std::string result;
  result.reserve(bitFieldSize - size + 1);
  for (uint32_t i = bitFieldSize - size; i < bitFieldSize; i++)
    result += tmp[i];
  return result;
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

#if defined(_MSC_VER)
#pragma warning(push)
#pragma warning(disable : 4505)  // unreferenced function with internal linkage
                                 // has been removed
#endif
// Copy everything that looks like a number into output iterator.
static void CopyNumberTo(const char *in_begin, const char *in_end,
                         char *out_begin, const char *out_end) {
  const char *src = in_begin;
  char *dst = out_begin;
  const char *extra_allowed = "+-.e";
  bool have_point = false;
  out_end -= 1;  // Allow space for 0 termination.
  while ((src < in_end) && (isdigit(*src) || strchr(extra_allowed, *src)) &&
         (dst < out_end)) {
    // The sign is only allowed in the first character of the buffer
    if (((*src == '+') || (*src == '-')) && (dst != out_begin)) break;
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
#if defined(_MSC_VER)
#pragma warning(pop)
#endif

template <typename T, T (*strto_fallback_fun)(const char *, char **)>
static const char *strToIeee(std::string_view s, T *result) {
  // Need to skip whitespace first to not use up our buffer for that.
  while (!s.empty() && isspace(s.front())) s.remove_prefix(1);
  if constexpr (from_chars_available_v<T>) {
    if (!s.empty() && (s.front() == '+')) s.remove_prefix(1);
    if (s.empty()) return nullptr;
    auto success = std::from_chars(s.data(), s.data() + s.size(), *result);
    return (success.ec == std::errc()) ? success.ptr : nullptr;
  } else {
    if (s.empty()) return nullptr;

    // Fallback in case std::from_chars() does not exist for this type. Here,
    // we just call the corresponding C-function, but first have to copy
    // the number to a local buffer, as that one requires \0-termination.
    char buffer[64] = {'\0'};

    CopyNumberTo(s.data(), s.data() + s.size(), buffer,
                 buffer + sizeof(buffer));
    char *endptr = nullptr;
    *result = strto_fallback_fun(buffer, &endptr);
    if (endptr == buffer) return nullptr;  // Error.

    // Now, convert our offset back relative to the original string.
    return s.data() + (endptr - buffer);
  }
}

const char *NumUtils::parseFloat(std::string_view s, float *result) {
  return strToIeee<float, strtof>(s, result);
}

const char *NumUtils::parseDouble(std::string_view s, double *result) {
  return strToIeee<double, strtod>(s, result);
}

const char *NumUtils::parseLongDouble(std::string_view s, long double *result) {
  return strToIeee<long double, strtold>(s, result);
}

}  // namespace SURELOG
