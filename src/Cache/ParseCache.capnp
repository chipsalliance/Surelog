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
# IDL for Parser cache.

@0xe809af0b198ce1a1;

using CACHE = import "Cache.capnp";

struct DesignElement {
  name            @0  :UInt64;
  fileId          @1  :UInt64;
  type            @2  :UInt32;
  uniqueId        @3  :UInt64;
  line            @4  :UInt32;
  column          @5  :UInt32;
  endLine         @6  :UInt32;
  endColumn       @7  :UInt32;
  timeInfo        @8  :CACHE.TimeInfo;
  parent          @9  :UInt64;
  node            @10 :UInt32;
  defaultNetType  @11 :UInt32;
}

struct ParseCache {
  header    @0 :CACHE.Header;
  errors    @1 :List(CACHE.Error);
  symbols   @2 :List(Text);
  elements  @3 :List(DesignElement);
  objects   @4 :List(CACHE.VObject);
}
