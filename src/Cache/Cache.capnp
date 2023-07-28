# Copyright 2019 Alain Dargelas
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Surelog
# IDL for Macro cache header.

@0xd682dc5d1dcaa153;

struct Header {
  # Making sure that we are compatible with whatever Surelog and schema
  # this is written.
  schemaVersion @0 :Text;  # schema version.
  slVersion     @1 :Text;  # Surelog version

  # No file-timestamp as this would violate hermetic build assumptions:
  # running the same tool on the same file must always yield the same cache.
  # Same is true for source filename as well.
}

struct Location {
  fileId  @0 :UInt64;
  line    @1 :UInt32;
  column  @2 :UInt16;
  object  @3 :UInt64;
}

struct Error {
  locations @0 :List(Location);
  errorId   @1 :UInt32;
}

struct TimeInfo {
  type                @0 :UInt16;
  fileId              @1 :UInt64;
  line                @2 :UInt32;
  timeUnit            @3 :UInt16;
  timeUnitValue       @4 :Float64;
  timePrecision       @5 :UInt16;
  timePrecisionValue  @6 :Float64;
}

# This is what we need to encode, but we limit all the UInt64 and UInt32 objects to
# 20 bits and the UInt16 stays at 16 bits for the line and 12 bits for the type
#
# struct VObject {
#   name        @0  :UInt64;
#   type        @1  :UInt16;
#   column      @2  :UInt16;
#   line        @3  :UInt32;
#   parent      @4  :UInt32;
#   definition  @5  :UInt32;
#   child       @6  :UInt32;
#   sibling     @7  :UInt32;
#   file        @8  :UInt64;
#   endLine     @9  :UInt32;
#   endColumn   @10 :UInt16;
# }
#
# It results in a compressed struct as below:

struct VObject {
  field1  @0 :UInt64;
  field2  @1 :UInt64;
  field3  @2 :UInt64;
  field4  @3 :UInt64;
}
