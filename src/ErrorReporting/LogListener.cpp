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
#include "LogListener.h"

using namespace SURELOG;

LogListener::LogResult LogListener::initialize(const std::string &filename) {
  std::ofstream strm(filename, std::fstream::out);
  if (!strm.good()) {
    return LogResult::FailedToOpenFileForWrite;
  }
  strm.close();

  std::scoped_lock lock(mutex);
  this->filename = filename;
  return LogResult::Ok;
}

std::string LogListener::getLogFilename() const {
  std::scoped_lock lock(mutex);
  return filename;
}

void LogListener::setMaxQueuedMessageCount(int count) {
  std::scoped_lock lock(mutex);
  maxQueuedMessageCount = count;
}

int LogListener::getMaxQueuedMessageCount() const {
  // Lock unnecessary here ...
  return maxQueuedMessageCount;
}

int LogListener::getQueuedMessageCount() const {
  std::scoped_lock lock(mutex);
  return static_cast<int>(queued.size());
}

void LogListener::enqueue(const std::string &message) {
  // NOTE: This isn't guarded since this is expected to be used only via
  // public API (which in turn are reponsible for ensuring thread-safety)

  while (queued.size() >= maxQueuedMessageCount) {
    queued.pop_front();
    ++droppedCount;
  }
  queued.push_back(message);
}

void LogListener::flush(std::ofstream &strm) {
  // NOTE: This isn't guarded since this is expected to be used only via
  // public API (which in turn are reponsible for ensuring thread-safety)

  if (droppedCount > 0) {
    strm << "---------- " << droppedCount
         << " messages were dropped! ----------" << std::endl;
  }
  droppedCount = 0;
  while (!queued.empty()) {
    strm << queued.front();
    queued.pop_front();
  }
  strm << std::flush;
}

LogListener::LogResult LogListener::flush() {
  std::scoped_lock lock(mutex);

  if (queued.empty()) {
    return LogResult::Ok;  // Nothing to flush!
  }

  std::ofstream strm(filename, std::fstream::app);
  if (!strm.good()) {
    return LogResult::FailedToOpenFileForWrite;
  }

  flush(strm);
  strm.close();
  return LogResult::Ok;
}

LogListener::LogResult LogListener::log(const std::string &message) {
  std::scoped_lock lock(mutex);

  if (filename.empty()) {
    enqueue(message);
    return LogResult::Enqueued;
  }

  std::ofstream strm(filename, std::fstream::app);
  if (!strm.good()) {
    enqueue(message);
    return LogResult::FailedToOpenFileForWrite;
  }

  if (!queued.empty()) {
    flush(strm);
  }

  strm << message << std::flush;
  strm.close();
  return LogResult::Ok;
}
