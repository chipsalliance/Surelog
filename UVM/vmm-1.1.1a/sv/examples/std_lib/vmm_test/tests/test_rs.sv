//
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    All Rights Reserved Worldwide
//
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
//


class rs_test_data extends alu_data;
  constraint cst_test {
    kind == RS;
  }
endclass

`vmm_test_begin(test_rs, alu_env, "Rightshift")
  env.build();
  begin
     rs_test_data tdata = new;
     env.gen.randomized_obj = tdata;
  end
  env.run();
`vmm_test_end(test_rs)
