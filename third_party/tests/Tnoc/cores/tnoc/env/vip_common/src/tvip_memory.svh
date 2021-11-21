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
`ifndef TVIP_MEMORY_SVH
`define TVIP_MEMORY_SVH
class tvip_memory #(
  int ADDRESS_WIDTH = 32,
  int DATA_WIDTH    = 32
) extends uvm_object;
  typedef bit [ADDRESS_WIDTH-1:0] tvip_memory_address;
  typedef bit [DATA_WIDTH-1:0]    tvip_memory_data;
  typedef bit [DATA_WIDTH/8-1:0]  tvip_memory_strobe;

            logic [DATA_WIDTH-1:0]  default_data;
  protected int                     byte_width;
  protected byte                    memory[tvip_memory_address];

  function new(string name = "tvip_memory", int data_width = DATA_WIDTH);
    super.new(name);
    default_data  = '0;
    byte_width    = data_width / 8;
  endfunction

  virtual function void put(
    tvip_memory_data    data,
    tvip_memory_strobe  strobe,
    int                 byte_size,
    tvip_memory_address base,
    int                 word_index
  );
    tvip_memory_address start_address;
    tvip_memory_address memory_address;
    int                 byte_index;

    start_address = get_start_address(byte_size, base, word_index);
    for (int i = 0;i < byte_size;++i) begin
      memory_address          = start_address + i;
      byte_index              = memory_address % byte_width;
      memory[memory_address]  = data[8*byte_index+:8];
    end
  endfunction

  virtual function tvip_memory_data get(
    int                 byte_size,
    tvip_memory_address base,
    int                 word_index
  );
    tvip_memory_data    data;
    tvip_memory_address start_address;
    tvip_memory_address memory_address;
    int                 byte_index;

    start_address = get_start_address(byte_size, base, word_index);
    for (int i = 0;i < byte_size;++i) begin
      memory_address  = start_address + i;
      byte_index      = memory_address % byte_width;
      if (memory.exists(memory_address)) begin
        data[8*byte_index+:8] = memory[memory_address];
      end
      else begin
        data[8*byte_index+:8] = get_default_data(byte_index);
      end
    end

    return data;
  endfunction

  virtual function bit exists(
    int                 byte_size,
    tvip_memory_address base,
    int                 word_index
  );
    tvip_memory_address start_address;
    tvip_memory_address memory_address;

    start_address = get_start_address(byte_size, base, word_index);
    for (int i = 0;i < byte_size;++i) begin
      memory_address  = start_address + i;
      if (memory.exists(memory_address)) begin
        return 1;
      end
    end

    return 0;
  endfunction

  protected function tvip_memory_address get_start_address(
    int                 byte_size,
    tvip_memory_address base,
    int                 word_index
  );
    return (base & get_address_mask(byte_size)) + byte_size * word_index;
  endfunction

  protected function tvip_memory_address get_address_mask(int byte_size);
    tvip_memory_address mask;
    mask  = byte_size - 1;
    mask  = ~mask;
    return mask;
  endfunction

  protected function byte get_default_data(int byte_index);
    if ($isunknown(default_data[8*byte_index+:8])) begin
      return $urandom_range(255);
    end
    else begin
      return default_data[8*byte_index+:8];
    end
  endfunction
endclass
`endif
