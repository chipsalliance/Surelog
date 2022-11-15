/*
 Copyright 2020 Alain Dargelas

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
 * File:   NumUtils.h
 * Author: alain
 *
 * Created on Dec 29, 2020, 10:43 PM
 */

#ifndef SURELOG_NUMUTILS_H
#define SURELOG_NUMUTILS_H
#pragma once

#include <cstdint>
#include <string>
#include <charconv>
#include <string_view>
#include <ctype.h>

namespace SURELOG {

// These functions parse a number from a std::string_view into "result".
// Returns the end of the number on success, nullptr otherwise.
// So this can be used in a simple boolean context for success testing, but
// as well in parsing context where advancing to the next position after the
// number is needed.
// All these functions require to check the return value to verify that parsing
// worked.

// Parse any number type with std::from_chars
namespace internal {
template <typename number_type>
const char *strto_num(std::string_view s, number_type *result) {
  while (!s.empty() && isspace(s.front())) s.remove_prefix(1);
  if (!s.empty() && s.front() == '+') s.remove_prefix(1);
  auto success = std::from_chars(s.data(), s.data() + s.size(), *result);
  return (success.ec == std::errc()) ? success.ptr : nullptr;
}

template <typename sint_type, typename uint_type, typename result_type>
const char *strto_int(std::string_view s, result_type *result) {
  // std::from_chars can't deal with leading spaces or plus, so remove them.
  while (!s.empty() && isspace(s.front())) s.remove_prefix(1);
  if (!s.empty() && s.front() == '+') s.remove_prefix(1);
  std::from_chars_result parse_result;
  if (s.front() == '-') {
    sint_type n;
    parse_result = std::from_chars(s.data(), s.data() + s.size(), n);
    *result = static_cast<result_type>(n);
  } else {
    uint_type n;
    parse_result = std::from_chars(s.data(), s.data() + s.size(), n);
    *result = static_cast<result_type>(n);
  }
  return (parse_result.ec == std::errc()) ? parse_result.ptr : nullptr;
}
}  // namespace internal

// Parse int values.
// Returns the pointer to one char after the parsed value or nullptr on failure.

// Parse integer of the given size (int32_t, uint32_t, int64_t, uint64_t),
// but be lenient in the sign interpretation.
// The full signed negative range and positive unsigned range for the integer
// of that size is allowed. The final value is cast to the signed or unsigned
// potentially flipping the sign (but we're leniently allowing that).
template <typename result_type>
[[nodiscard]] inline const char* parse_int_lenient(std::string_view s,
                                                   result_type* result) {
 if constexpr (sizeof(result_type) == 4) {
    return internal::strto_int<int32_t, uint32_t, result_type>(s, result);
  } else  {
    return internal::strto_int<int64_t, uint64_t, result_type>(s, result);
  }
}

  // Parse signed int32, stricly matching its range
[[nodiscard]] inline const char* parse_int32(std::string_view s,
                                             int32_t* result) {
  return internal::strto_num(s, result);
}
    // Parse uint32, stricly matching its range; no negative numbers
[[nodiscard]] inline const char* parse_uint32(std::string_view s,
                                              uint32_t* result) {
  return internal::strto_num(s, result);
}

  // Parse signed int64, stricly matching its range; no negative numbers
[[nodiscard]] inline const char* parse_int64(std::string_view s,
                                             int64_t* result) {
  return internal::strto_num(s, result);
}

    // Parse uint64, stricly matching its range; no negative numbers
[[nodiscard]] inline const char* parse_uint64(std::string_view s,
                                              uint64_t* result) {
  return internal::strto_num(s, result);
}

// Parse float value.
// Returns the pointer to one char after the parsed value or nullptr on failure.
[[nodiscard]] const char* parse_float(std::string_view s, float* result);

// Parse double value.
// Returns the pointer to one char after the parsed value or nullptr on failure.
[[nodiscard]] const char* parse_double(std::string_view s, double* result);

// Parse long double value.
// Returns the pointer to one char after the parsed value or nullptr on failure.
[[nodiscard]] const char *parse_longdouble(std::string_view s,
                                           long double *result);

class NumUtils final {
 public:
  static std::string hexToBin(const std::string &s);

  static std::string binToHex(const std::string &s);

  static std::string toBinary(int size, uint64_t val);

  static std::string trimLeadingZeros(const std::string &s);

  static uint64_t getMask(uint64_t wide);

 private:
  NumUtils() = delete;
  NumUtils(const NumUtils &orig) = delete;
  ~NumUtils() = delete;

 private:
};

};  // namespace SURELOG

#endif /* SURELOG_NUMUTILS_H */
