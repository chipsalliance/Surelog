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
`ifndef TUE_REG_BIT_BASH_SEQ_SVH
`define TUE_REG_BIT_BASH_SEQ_SVH
class tue_reg_single_bit_bash_seq extends tue_reg_sequence_base #(uvm_reg_single_bit_bash_seq);
  task body();
    int unsigned  n_bits;
    uvm_reg_field fields[$];
    uvm_reg_map   maps[$];

    if (rg == null) begin
      `uvm_error(
        get_type_name(),
        "No register specified to run sequence on"
      )
      return;
    end

    if (!is_reg_test_executed(rg, "REG_BIT_BASH_TEST")) begin
      return;
    end

    n_bits  = rg.get_n_bytes() * 8;
    rg.get_fields(fields);
    rg.get_maps(maps);
    foreach (maps[i]) begin
      uvm_reg_data_t  dc_mask;
      string          mode[int];

      if (!is_reg_readable(rg, maps[i])) begin
        `uvm_warning(
          get_type_name(),
          $sformatf(
            "Register %s is write-only register in map %s, skipping",
            rg.get_full_name(), maps[i].get_full_name()
          )
        )
        continue;
      end

      `uvm_info(
        get_type_name(),
        $sformatf(
          "Verifying bits in register \"%s\" in map \"%s\" ...",
          rg.get_full_name(), maps[i].get_full_name()
        ),
        UVM_LOW
      )

      check_field_accesses(fields, maps[i], n_bits, dc_mask, mode);
      for (int j = 0;j < n_bits;++j) begin
        string  bit_mode;

        if (dc_mask[j]) begin
          continue;
        end

        bit_mode  = (mode.exists(j)) ? mode[j] : "RO";
        bash_kth_bit(rg, j, bit_mode, maps[i], dc_mask);
      end
    end
  endtask

  protected function void check_field_accesses(
    const ref uvm_reg_field   fields[$],
    input     uvm_reg_map     map,
    input     int unsigned    n_bits,
    ref       uvm_reg_data_t  dc_mask,
    ref       string          mode[int]
  );
    uvm_reg_data_t  check_mask;

    check_mask  = '0;
    foreach (fields[i]) begin
      int     lsb;
      int     width;
      bit     check;
      string  access;

      lsb     = fields[i].get_lsb_pos();
      width   = fields[i].get_n_bits();
      check   = is_field_readable(fields[i], map) && (fields[i].get_compare() == UVM_CHECK);
      access  = fields[i].get_access(map);

      for (int j = 0;j < width;++j) begin
        check_mask[j+lsb] = check;
        mode[j+lsb]       = access;
      end
    end

    dc_mask = (~check_mask) & ((1 << n_bits) - 1);
  endfunction

  `tue_object_default_constructor(tue_reg_single_bit_bash_seq)
  `uvm_object_utils(tue_reg_single_bit_bash_seq)
endclass

class tue_reg_bit_bash_seq extends uvm_reg_bit_bash_seq;
  task body();
    if (model == null) begin
      `uvm_error(
        get_type_name(),
        "No register model specified to run sequence on"
      )
      return;
    end

    `uvm_info(
      "STARTING_SEQ", $sformatf("\n\nStarting %s sequence...\n", get_name()), UVM_LOW
    )

    reset_blk(model);
    model.reset();

    reg_seq = create_reg_sequence();
    do_block(model);
  endtask

  protected virtual function uvm_reg_single_bit_bash_seq create_reg_sequence();
    return tue_reg_single_bit_bash_seq::type_id::create("reg_single_bit_bash_seq");
  endfunction

  `tue_object_default_constructor(tue_reg_bit_bash_seq)
  `uvm_object_utils(tue_reg_bit_bash_seq)
endclass
`endif
