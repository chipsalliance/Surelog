//------------------------------------------------------------------------------
//  Copyright 2018 Taichi Ishitani
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
`ifndef TUE_FIFO_SVH
`define TUE_FIFO_SVH
class tue_fifo #(
  type  T = int
) extends uvm_object;
  local mailbox #(T)  mb;
  local int           m_size;

  function new(string name = "tue_fifo", int size = 1);
    super.new(name);
    mb      = new(size);
    m_size  = size;
  endfunction

  virtual function int size();
    return m_size;
  endfunction

  virtual function int used();
    return mb.num();
  endfunction

  virtual function bit is_empty();
    return (used() == 0) ? 1 : 0;
  endfunction

  virtual function bit is_full();
    return ((m_size >= 1) && (used() == m_size)) ? 1 : 0;
  endfunction

  virtual task put(T t);
    mb.put(t);
  endtask

  virtual task get(output T t);
    mb.get(t);
  endtask

  virtual task peek(output T t);
    mb.peek(t);
  endtask

  virtual function bit try_get(output T t);
    return mb.try_get(t);
  endfunction

  virtual function bit try_put(T t);
    return mb.try_put(t);
  endfunction

  virtual function bit try_peek(output T t);
    return mb.try_peek(t);
  endfunction
endclass
`endif
