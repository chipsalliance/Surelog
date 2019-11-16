// $Id: //dvt/vtech/dev/main/ovm-tests/examples/hello_world/ovm/consumer.sv#1 $
//----------------------------------------------------------------------
//   Copyright 2007-2009 Mentor Graphics Corporation
//   Copyright 2007-2009 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------

class consumer #(type T=packet) extends ovm_component;

  ovm_blocking_put_imp #(T,consumer #(T)) in;
  ovm_get_port #(T) out;

  function new(string name, ovm_component parent=null);
    super.new(name,parent);
    in=new("in",this);
    out=new("out",this,0);
  endfunction

  protected int count=0;
  local semaphore lock = new(1);

  `ovm_component_utils_begin(consumer #(T))
    `ovm_field_int(count,OVM_ALL_ON + OVM_READONLY + OVM_DEC)
  `ovm_component_utils_end

  task run ();
    T p;
    while(out.size()) begin
      out.get(p);
      put(p);
    end
  endtask

  task put (T p);
    lock.get();
    count++;
//    void'(accept_tr(p));
    accept_tr(p);
    #10;
    void'(begin_tr(p));
    #30; 
    end_tr(p); 
    `ovm_info("consumer", $sformatf("Received %0s local_count=%0d",p.get_name(),count), OVM_MEDIUM)
    if (`ovm_msg_detail(OVM_HIGH))
      p.print();
    lock.put();
  endtask 
endclass

