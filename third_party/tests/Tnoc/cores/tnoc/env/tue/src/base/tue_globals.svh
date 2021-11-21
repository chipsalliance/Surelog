//------------------------------------------------------------------------------
//  Copyright 2017 Taichi Ishitani
//
//  Licensed under the Apache License, Version 2.0 (the "License");
//  you may not use this file except in compliance with the License.
//  You may obtain a copy of the License at
//
//  http://www.apache.org/licenses/LICENSE-2.0
//
//  Unless required by applicable law or agreed to in writing, software
//  distributed under the License is distributed on an "AS IS" BASIS,
//  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//  See the License for the specific language governing permissions and
//  limitations under the License.
//------------------------------------------------------------------------------
`ifndef TUE_GLOBALS_SVH
`define TUE_GLOBALS_SVH

function automatic string tue_concat_paths(
  string  parent_path,
  string  child_path,
  string  separator = "."
);
  if (child_path.len() == 0) begin
    return parent_path;
  end
  else if (parent_path.len() == 0) begin
    return child_path;
  end
  else begin
    return {parent_path, separator, child_path};
  end
endfunction

`endif
