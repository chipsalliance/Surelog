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

#ifndef LOGLISTENER_H
#define LOGLISTENER_H

#include <deque>
#include <fstream>
#include <mutex>
#include <string>

namespace SURELOG {
// A thread-safe log listener that flushes it contents to a named file on disk.
// Supports caching a fixed number of messages if the messages arrives before
// the listener is initialized.
class LogListener {
 private:
  static constexpr unsigned int DEFAULT_MAX_QUEUED_MESSAGE_COUNT = 100;

 public:
  enum class LogResult {
    FailedToOpenFileForWrite = -1,
    Ok = 0,
    Enqueued = 1,
  };

  static bool succeeded(LogResult result) {
    return static_cast<int>(result) >= 0;
  }

  static bool failed(LogResult result) { return static_cast<int>(result) < 0; }

 public:
  LogListener() = default;
  virtual ~LogListener() = default;  // virtual as used as interface

  virtual LogResult initialize(const std::string& filename);

  virtual void setMaxQueuedMessageCount(int count);
  int getMaxQueuedMessageCount() const;

  std::string getLogFilename() const;
  int getQueuedMessageCount() const;

  virtual LogResult log(const std::string& message);
  virtual LogResult flush();

 protected:
  // NOTE: Internal protected/private methods aren't thread-safe.
  void enqueue(const std::string& message);
  void flush(std::ofstream& strm);

 protected:
  std::string filename;
  mutable std::mutex mutex;
  std::deque<std::string> queued;
  int droppedCount = 0;
  unsigned int maxQueuedMessageCount = DEFAULT_MAX_QUEUED_MESSAGE_COUNT;

 private:
  LogListener(const LogListener&) = delete;
  LogListener& operator=(const LogListener&) = delete;
};

}  // namespace SURELOG

#endif /* LOGLISTENER_H */
