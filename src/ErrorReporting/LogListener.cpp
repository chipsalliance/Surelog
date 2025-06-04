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

#include <cstdint>
#include <iostream>
#include <string_view>

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/PathId.h"
#include "Surelog/Common/Session.h"

namespace SURELOG {
LogListener::LogListener(Session *session) : m_session(session) {}

LogListener::LogResult LogListener::initialize() {
  FileSystem *const fileSystem = m_session->getFileSystem();
  CommandLineParser *const clp = m_session->getCommandLineParser();
  PathId fileId = clp->getLogFileId();
  std::ostream &strm = fileSystem->openForWrite(fileId);
  if (!strm.good()) {
    fileSystem->close(strm);
    return LogResult::FailedToOpenFileForWrite;
  }
  fileSystem->close(strm);

  std::scoped_lock<std::mutex> lock(m_mutex);
  m_fileId = fileId;
  return LogResult::Ok;
}

PathId LogListener::getLogFileId() const {
  std::scoped_lock<std::mutex> lock(m_mutex);
  return m_fileId;
}

void LogListener::setMaxQueuedMessageCount(int32_t count) {
  std::scoped_lock<std::mutex> lock(m_mutex);
  m_maxQueuedMessageCount = count;
}

int32_t LogListener::getMaxQueuedMessageCount() const {
  // Lock unnecessary here ...
  return m_maxQueuedMessageCount;
}

int32_t LogListener::getQueuedMessageCount() const {
  std::scoped_lock<std::mutex> lock(m_mutex);
  return static_cast<int32_t>(m_queued.size());
}

void LogListener::enqueue(std::string_view message) {
  // NOTE: This isn't guarded since this is expected to be used only via
  // public API (which in turn are reponsible for ensuring thread-safety)

  while (m_queued.size() >= m_maxQueuedMessageCount) {
    m_queued.pop_front();
    ++m_droppedCount;
  }
  m_queued.emplace_back(message);
}

void LogListener::flush(std::ostream &strm) {
  // NOTE: This isn't guarded since this is expected to be used only via
  // public API (which in turn are reponsible for ensuring thread-safety)

  if (m_droppedCount > 0) {
    strm << "---------- " << m_droppedCount
         << " messages were dropped! ----------" << std::endl;
  }
  m_droppedCount = 0;
  while (!m_queued.empty()) {
    strm << m_queued.front();
    m_queued.pop_front();
  }
  strm << std::flush;
}

LogListener::LogResult LogListener::flush() {
  std::scoped_lock<std::mutex> lock(m_mutex);

  if (m_queued.empty()) {
    return LogResult::Ok;  // Nothing to flush!
  }

  FileSystem *const fileSystem = m_session->getFileSystem();

  std::ostream &strm =
      fileSystem->openOutput(m_fileId, std::ios_base::out | std::ios_base::app);
  if (!strm.good()) {
    fileSystem->close(strm);
    return LogResult::FailedToOpenFileForWrite;
  }

  flush(strm);
  fileSystem->close(strm);
  return LogResult::Ok;
}

LogListener::LogResult LogListener::log(std::string_view message) {
  std::scoped_lock<std::mutex> lock(m_mutex);

  if (!m_fileId) {
    enqueue(message);
    return LogResult::Enqueued;
  }

  FileSystem *const fileSystem = m_session->getFileSystem();

  std::ostream &strm =
      fileSystem->openOutput(m_fileId, std::ios_base::out | std::ios_base::app);
  if (!strm.good()) {
    enqueue(message);
    fileSystem->close(strm);
    return LogResult::FailedToOpenFileForWrite;
  }

  if (!m_queued.empty()) {
    flush(strm);
  }

  strm << message << std::flush;
  fileSystem->close(strm);
  return LogResult::Ok;
}

}  // namespace SURELOG
