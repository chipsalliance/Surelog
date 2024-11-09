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

#include "Surelog/ErrorReporting/LogListener.h"

#include <iostream>
#include <string_view>

#include "Surelog/Common/FileSystem.h"

namespace SURELOG {

LogListener::LogResult LogListener::initialize(PathId fileId) {
  FileSystem *const fileSystem = FileSystem::getInstance();
  std::ostream &strm = fileSystem->openForWrite(fileId);
  if (!strm.good()) {
    fileSystem->close(strm);
    return LogResult::FailedToOpenFileForWrite;
  }
  fileSystem->close(strm);

  std::scoped_lock<std::mutex> lock(mutex);
  this->fileId = fileId;
  return LogResult::Ok;
}

PathId LogListener::getLogFileId() const {
  std::scoped_lock<std::mutex> lock(mutex);
  return fileId;
}

void LogListener::setMaxQueuedMessageCount(int32_t count) {
  std::scoped_lock<std::mutex> lock(mutex);
  maxQueuedMessageCount = count;
}

int32_t LogListener::getMaxQueuedMessageCount() const {
  // Lock unnecessary here ...
  return maxQueuedMessageCount;
}

int32_t LogListener::getQueuedMessageCount() const {
  std::scoped_lock<std::mutex> lock(mutex);
  return static_cast<int32_t>(queued.size());
}

void LogListener::enqueue(std::string_view message) {
  // NOTE: This isn't guarded since this is expected to be used only via
  // public API (which in turn are reponsible for ensuring thread-safety)

  while (queued.size() >= maxQueuedMessageCount) {
    queued.pop_front();
    ++droppedCount;
  }
  queued.emplace_back(message);
}

void LogListener::flush(std::ostream &strm) {
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
  std::scoped_lock<std::mutex> lock(mutex);

  if (queued.empty()) {
    return LogResult::Ok;  // Nothing to flush!
  }

  FileSystem *const fileSystem = FileSystem::getInstance();
  std::ostream &strm =
      fileSystem->openOutput(fileId, std::ios_base::out | std::ios_base::app);
  if (!strm.good()) {
    fileSystem->close(strm);
    return LogResult::FailedToOpenFileForWrite;
  }

  flush(strm);
  fileSystem->close(strm);
  return LogResult::Ok;
}

LogListener::LogResult LogListener::log(std::string_view message) {
  std::scoped_lock<std::mutex> lock(mutex);

  if (!fileId) {
    enqueue(message);
    return LogResult::Enqueued;
  }

  FileSystem *const fileSystem = FileSystem::getInstance();
  std::ostream &strm =
      fileSystem->openOutput(fileId, std::ios_base::out | std::ios_base::app);
  if (!strm.good()) {
    enqueue(message);
    fileSystem->close(strm);
    return LogResult::FailedToOpenFileForWrite;
  }

  if (!queued.empty()) {
    flush(strm);
  }

  strm << message << std::flush;
  fileSystem->close(strm);
  return LogResult::Ok;
}

}  // namespace SURELOG
