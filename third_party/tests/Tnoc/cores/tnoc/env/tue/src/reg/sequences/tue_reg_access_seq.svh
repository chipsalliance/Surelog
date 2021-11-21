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
`ifndef TUE_REG_ACCESS_SEQ_SVH
`define TUE_REG_ACCESS_SEQ_SVH
class tue_reg_single_access_seq extends tue_reg_sequence_base #(uvm_reg_single_access_seq);
  task body();
    uvm_reg_map   maps[$];
    uvm_reg_field fields[$];

    if (rg == null) begin
      `uvm_error(
        get_type_name(),
        "No register specified to run sequence on"
      )
      return;
    end

    if (!is_reg_test_executed(rg, "REG_ACCESS_TEST")) begin
      return;
    end

    if (!check_backdoor()) begin
      `uvm_error(
        get_type_name(),
        $sformatf(
          "Register '%s' does not have a backdoor mechanism available",
          rg.get_full_name()
        )
      )
      return;
    end

    rg.get_maps(maps);
    rg.get_fields(fields);
    foreach (maps[i]) begin
      if (includes_unknown_access(fields, maps[i])) begin
        continue;
      end
      if (!is_reg_writable(rg, maps[i])) begin
        `uvm_warning(
          get_type_name(),
          $sformatf(
            "Register '%s' is read-only in map '%s', skipping",
            rg.get_full_name(), maps[i].get_full_name()
          )
        )
        continue;
      end

      verify_access(maps[i]);
    end
  endtask

  protected function bit check_backdoor();
    if (rg.get_backdoor() != null) begin
      return 1;
    end
    else if (rg.has_hdl_path()) begin
      return 1;
    end
    else begin
      return 0;
    end
  endfunction

  protected function bit includes_unknown_access(
    const ref uvm_reg_field fields[$],
    input     uvm_reg_map   map
  );
    foreach (fields[i]) begin
      if (!fields[i].is_known_access(map)) begin
        `uvm_warning(
          get_type_name(),
          $sformatf(
            "Register '%s' has field with unknown access type '%s', skipping",
            rg.get_full_name(), fields[i].get_access(map)
          )
        )
        return 1;
      end
    end
    return 0;
  endfunction

  protected virtual task verify_access(uvm_reg_map map);
    uvm_status_e    status;
    uvm_reg_data_t  value;

    `uvm_info(
      get_type_name(),
      $sformatf(
        "Verifying access of register '%s' in map '%s' ...",
        rg.get_full_name(), map.get_full_name()
      ),
      UVM_LOW
    )

    value = rg.get();

    rg.write(status, ~value, UVM_FRONTDOOR, map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error(
        get_type_name(),
        $sformatf(
          "Status was '%s' when writing '%s' register through map '%s'",
          status.name(), rg.get_full_name(), map.get_full_name()
        )
      )
    end
    #1;

    rg.mirror(status, UVM_CHECK, UVM_BACKDOOR, map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error(
        get_type_name(),
        $sformatf(
          "Status was '%s' when reading '%s' register through backdoor",
          status.name(), rg.get_full_name()
        )
      )
    end

    if (!is_reg_readable(rg, map)) begin
      return;
    end

    rg.write(status, value, UVM_BACKDOOR, map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error(
        get_type_name(),
        $sformatf(
          "Status was '%s' when writing '%s' register through backdoor",
          status.name(), rg.get_full_name()
        )
      )
    end

    rg.mirror(status, UVM_CHECK, UVM_FRONTDOOR, map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error(
        get_type_name(),
        $sformatf(
          "Status was '%s' when reading '%s' register through map '%s'",
          status.name(), rg.get_full_name(), map.get_full_name()
        )
      )
    end
  endtask

  `tue_object_default_constructor(tue_reg_single_access_seq)
  `uvm_object_utils(tue_reg_single_access_seq)
endclass

class tue_reg_access_seq extends uvm_reg_access_seq;
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

  protected virtual function uvm_reg_single_access_seq create_reg_sequence();
    return tue_reg_single_access_seq::type_id::create("single_reg_access_seq");
  endfunction

  `tue_object_default_constructor(tue_reg_access_seq)
  `uvm_object_utils(tue_reg_access_seq)
endclass
`endif
