// $Id: //dvt/vtech/dev/main/ovm-tests/examples/hello_world/ovm/producer.sv#1 $
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

class producer #(type T=packet) extends ovm_component;

  ovm_blocking_put_port #(T) out;

  function new(string name, ovm_component parent=null);
    super.new(name,parent);
    out = new("out",this);
    void'(get_config_int("num_packets", this.num_packets));
  endfunction

  protected T   proto       = new;
  protected int num_packets = 1;
  protected int count       = 0;

  `ovm_component_utils_begin(producer #(T))
    `ovm_field_object(proto, OVM_ALL_ON + OVM_REFERENCE)
    `ovm_field_int(num_packets, OVM_ALL_ON + OVM_DEC)
    `ovm_field_int(count, OVM_ALL_ON + OVM_DEC + OVM_READONLY)
  `ovm_component_utils_end

  task run();
    T p;
    string image, num;

    `ovm_info("producer", "Starting.", OVM_MEDIUM)

    for (count =0; count < num_packets; count++) begin

      $cast(p, proto.clone());

      num.itoa(count);
      p.set_name({get_name(),"-",num});

      p.set_initiator(this);

      if (ovm_verbosity'(recording_detail)!=OVM_NONE)
        p.enable_recording("packet_stream");

      void'(p.randomize());

      `ovm_info("producer", $sformatf("Sending %s",p.get_name()), OVM_MEDIUM)

      if (`ovm_msg_detail(OVM_HIGH))
        p.print();

      out.put(p);

      #10;

    end

    `ovm_info("producer", "Exiting.", OVM_MEDIUM)

  endtask

endclass

