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
 * File:   Timer.h
 * Author: alain
 *
 * Created on September 25, 2018, 7:48 PM
 */

#ifndef SURELOG_TIMER_H
#define SURELOG_TIMER_H
#pragma once

#include <chrono>
#include <cmath>
#include <iostream>

namespace SURELOG {

class Timer final {
 public:
  Timer() : m_beg(clock_t::now()) {}

  void reset() { m_beg = clock_t::now(); }

  double elapsed() const {
    return std::chrono::duration_cast<second_t>(clock_t::now() - m_beg).count();
  }

  double elapsed_rounded() const {
    double res =
        std::chrono::duration_cast<second_t>(clock_t::now() - m_beg).count();
    return round(res);
  }

  double round(double f) const {
    return floor(f * 500 + 0.5) / 500;
    // return std::round(f * 5) / 5; // C++11
  }

 private:
  using clock_t = std::chrono::high_resolution_clock;
  using second_t = std::chrono::duration<double, std::ratio<1>>;
  std::chrono::time_point<clock_t> m_beg;
};

};  // namespace SURELOG

#endif /* SURELOG_TIMER_H */
