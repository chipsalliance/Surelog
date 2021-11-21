//------------------------------------------------------------------------------
//  Copyright 2020 Taichi Ishitani
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
`ifndef TUE_REG_HW_RESET_SEQ_SVH
`define TUE_REG_HW_RESET_SEQ_SVH
class tue_reg_hw_reset_seq extends tue_reg_sequence_base #(uvm_reg_hw_reset_seq);
  task body();
    if (model == null) begin
      `uvm_error(
        get_type_name(),
        "Not block or system specified to run sequence on"
      )
      return;
    end

    `uvm_info(
      "STARTING_SEQ", $sformatf("\n\nStarting %s sequence...\n", get_name()), UVM_LOW
    )

    reset_blk(model);
    model.reset();
    do_block(model);
  endtask

  protected task do_block(uvm_reg_block blk);
    uvm_reg       regs[$];
    uvm_reg_block blocks[$];

    if (!is_reg_test_executed(blk, "REG_HW_RESET_TEST")) begin
      return;
    end

    blk.get_registers(regs, UVM_NO_HIER);
    foreach (regs[i]) begin
      do_reg(regs[i]);
    end

    blk.get_blocks(blocks);
    foreach (blocks[i]) begin
      do_block(blocks[i]);
    end
  endtask

  protected virtual task do_reg(uvm_reg rg);
    uvm_reg_map   maps[$];
    uvm_reg_field fields[$];

    if (!is_reg_test_executed(rg, "REG_HW_RESET_TEST")) begin
      return;
    end

    rg.get_maps(maps);
    rg.get_fields(fields);
    foreach (maps[i]) begin
      uvm_check_e field_checks[uvm_reg_field];

      if (!is_reg_readable(rg, maps[i])) begin
        `uvm_warning(
          get_type_name(),
          $sformatf(
            "Register %s is write-only in map %s, skipping",
            rg.get_full_name(), maps[i].get_full_name()
          )
        )
        continue;
      end

      foreach (fields[j]) begin
        if (!is_target_field(fields[j], maps[i])) begin
          field_checks[fields[j]] = fields[j].get_compare();
          fields[j].set_compare(UVM_NO_CHECK);
        end
      end

      if (fields.size() != field_checks.size()) begin
        uvm_status_e  status;

        `uvm_info(
          "tue_reg_hw_reset_seq",
          $sformatf(
            "Verifying reset value of register %s in map %s ...",
            rg.get_full_name(), maps[i].get_full_name()
          ),
          UVM_LOW
        )

        rg.mirror(status, UVM_CHECK, UVM_FRONTDOOR, maps[i], this);
        if (status != UVM_IS_OK) begin
          `uvm_error(
            get_type_name(),
            $sformatf(
              "Status was %s when reading value of register \"%s\" through map \"%s\".",
              status.name(), rg.get_full_name(), maps[i].get_full_name()
            )
          )
        end

        foreach (field_checks[field]) begin
          field.set_compare(field_checks[field]);
        end
      end
    end
  endtask

  protected function is_target_field(uvm_reg_field field, uvm_reg_map map);
    if (!field.has_reset()) begin
      return 0;
    end
    else if (field.get_compare() == UVM_NO_CHECK) begin
      return 0;
    end
    else if (!is_field_readable(field, map)) begin
      return 0;
    end
    else if (!is_reg_test_executed(field, "REG_HW_RESET_TEST")) begin
      return 0;
    end
    else begin
      return 1;
    end
  endfunction

  `tue_object_default_constructor(tue_reg_hw_reset_seq)
  `uvm_object_utils(tue_reg_hw_reset_seq)
endclass
`endif
