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

enum MacroDefType {
  define      @0;
  undefine    @1;
  undefineAll @2;
}

struct LineColumn {
  line    @0 :UInt32;
  column  @1 :UInt16;
}

struct Macro {
  nameId            @0  :UInt32;
  defType           @1  :MacroDefType;
  fileId            @2  :UInt32;
  startLine         @3  :UInt32;
  startColumn       @4  :UInt16;
  endLine           @5  :UInt32;
  endColumn         @6  :UInt16;
  nameColumn        @7  :UInt16;
  bodyColumn        @8  :UInt16;
  arguments         @9  :List(Text);
  argumentPositions @10 :List(LineColumn);
  tokens            @11 :List(Text);
  tokenPositions    @12 :List(LineColumn);
}

struct IncludeFileInfo {
  action          @0  :UInt16;  # 1 or 2, push or pop
  context         @1  :UInt16;
  definition      @2  :Int32;
  sectionFileId   @3  :UInt64;
  sectionLine     @4  :UInt32;
  sourceLine      @5  :UInt32;
  sectionColumn   @6  :UInt16;
  sourceColumn    @7  :UInt16;
  symbolId        @8  :UInt32;
  symbolLine      @9  :UInt32;
  symbolColumn    @10 :UInt16;
  indexOpposite   @11 :Int32;
  definitions     @12 :List(UInt16);
  tokenPositions  @13 :List(LineColumn);
}

struct LineTranslationInfo {
  pretendFileId @0 :UInt64;
  originalLine  @1 :UInt32;
  pretendLine   @2 :UInt32;
}

struct PPCache {
  header            @0  :CACHE.Header;
  globalMacros      @1  :List(Macro);
  localMacros       @2  :List(UInt16);
  body              @3  :Text;
  errors            @4  :List(CACHE.Error);
  symbols           @5  :List(Text);
  defines           @6  :List(Text);
  timeInfos         @7  :List(CACHE.TimeInfo);
  lineTranslations  @8  :List(LineTranslationInfo);
  includeFileInfos  @9  :List(IncludeFileInfo);
  objects           @10 :List(CACHE.VObject);
}
