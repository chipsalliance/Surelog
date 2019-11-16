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


class alu_sb;

  vmm_log log;
  int num_trans = 0;

  function new(string name = "ALU_CHECKER");
    log = new("alu_sb", name);
  endfunction

  virtual function void check_transaction(alu_data tr);
    num_trans++;
    case(tr.kind)
      alu_data::ADD: begin
                       bit [6:0] exp = tr.a + tr.b;
                       if (tr.y == exp)
                         `vmm_trace(log, tr.psdisplay("TXN OK"));
                       else
                         `vmm_error(log, $psprintf("Output Mismatch!! Expected=%b, Actual=%b", (tr.a + tr.b), tr.y));
                     end
      alu_data::SUB: begin
                       bit [6:0] exp = tr.a - tr.b;
                       if (tr.y == exp)
                         `vmm_trace(log, tr.psdisplay("TXN OK"));
                       else
                         `vmm_error(log, $psprintf("Output Mismatch!! Expected=%b, Actual=%b", (tr.a - tr.b), tr.y));
                     end
      alu_data::MUL: begin
                       bit [6:0] exp = tr.a * tr.b;
                       if (tr.y == exp)
                         `vmm_trace(log, tr.psdisplay("TXN OK"));
                       else
                         `vmm_error(log, $psprintf("Output Mismatch!! Expected=%b, Actual=%b", (tr.a * tr.b), tr.y));
                     end
      alu_data::LS: begin
                       bit [6:0] exp = tr.a << 1;
                       if (tr.y == exp) 
                         `vmm_trace(log, tr.psdisplay("TXN OK"));
                       else
                         `vmm_error(log, $psprintf("Output Mismatch!! Expected=%b, Actual=%b", exp, tr.y));
                     end
      alu_data::RS: begin
                       bit [3:0] exp = tr.a >> 1;
                       if (tr.y == exp) 
                         `vmm_trace(log, tr.psdisplay("TXN OK"));
                       else
                         `vmm_error(log, $psprintf("Output Mismatch!! Expected=%b, Actual=%b", exp, tr.y));
                     end
    endcase
  endfunction

  virtual function void report();
     `vmm_note(log, $psprintf("Total Number of Transactions = %0d", num_trans));
  endfunction

endclass
