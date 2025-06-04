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
 * File:   LogListener.h
 * Author: hs
 *
 * Created on March 10, 2021, 9:30 PM
 */

#ifndef SURELOG_LOGLISTENER_H
#define SURELOG_LOGLISTENER_H
#pragma once

#include <Surelog/Common/PathId.h>

#include <cstdint>
#include <deque>
#include <mutex>
#include <ostream>
#include <string>
#include <string_view>

namespace SURELOG {
class Session;

// A thread-safe log listener that flushes it contents to a named file on disk.
// Supports caching a fixed number of messages if the messages arrives before
// the listener is initialized.
class LogListener {
 private:
  static constexpr uint32_t DEFAULT_MAX_QUEUED_MESSAGE_COUNT = 100;

 public:
  enum class LogResult {
    FailedToOpenFileForWrite = -1,
    Ok = 0,
    Enqueued = 1,
  };

  static bool succeeded(LogResult result) {
    return static_cast<int32_t>(result) >= 0;
  }

  static bool failed(LogResult result) {
    return static_cast<int32_t>(result) < 0;
  }

 public:
  explicit LogListener(Session* session);
  virtual ~LogListener() = default;  // virtual as used as interface

  virtual LogResult initialize();

  virtual void setMaxQueuedMessageCount(int32_t count);
  int32_t getMaxQueuedMessageCount() const;

  PathId getLogFileId() const;
  int32_t getQueuedMessageCount() const;

  virtual LogResult log(std::string_view message);
  virtual LogResult flush();

 protected:
  // NOTE: Internal protected/private methods aren't thread-safe.
  void enqueue(std::string_view message);
  void flush(std::ostream& strm);

 protected:
  Session* const m_session = nullptr;
  PathId m_fileId;
  mutable std::mutex m_mutex;
  std::deque<std::string> m_queued;
  int32_t m_droppedCount = 0;
  uint32_t m_maxQueuedMessageCount = DEFAULT_MAX_QUEUED_MESSAGE_COUNT;

 public:
  LogListener(const LogListener&) = delete;
  LogListener& operator=(const LogListener&) = delete;
};

}  // namespace SURELOG

#endif /* SURELOG_LOGLISTENER_H */
