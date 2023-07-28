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
# IDL for Preprocessor Macro cache.

@0xcaf26cf804094cc0;

using CACHE = import "Cache.capnp";

enum MacroType {
  noArgs    @0;
  withArgs  @1;
}

struct Macro {
  nameId      @0 :UInt64;
  type        @1 :MacroType;
  fileId      @2 :UInt32;
  startLine   @3 :UInt32;
  startColumn @4 :UInt16;
  endLine     @5 :UInt32;
  endColumn   @6 :UInt16;
  arguments   @7 :List(Text);
  tokens      @8 :List(Text);
}

struct IncludeFileInfo {
  context             @0  :UInt32;
  sectionStartLine    @1  :UInt32;
  sectionSymbolId     @2  :UInt64;
  sectionFileId       @3  :UInt64;
  originalStartLine   @4  :UInt32;
  originalStartColumn @5  :UInt32;
  originalEndLine     @6  :UInt32;
  originalEndColumn   @7  :UInt32;
  action              @8  :UInt32;  # 1 or 2, push or pop
  indexOpening        @9  :Int32;
  indexClosing        @10 :Int32;
}

struct LineTranslationInfo {
  pretendFileId @0 :UInt64;
  originalLine  @1 :UInt32;
  pretendLine   @2 :UInt32;
}

struct PPCache {
  header            @0 :CACHE.Header;
  macros            @1 :List(Macro);
  body              @2 :Text;
  errors            @3 :List(CACHE.Error);
  symbols           @4 :List(Text);
  defines           @5 :List(Text);
  timeInfos         @6 :List(CACHE.TimeInfo);
  lineTranslations  @7 :List(LineTranslationInfo);
  includeFileInfos  @8 :List(IncludeFileInfo);
  objects           @9 :List(CACHE.VObject);
}
