interface sample_bus_if(input clk, input rst_n);
  logic       req;
  logic       ack;
  logic       is_write;
  logic [2:0] address;
  logic [7:0] write_data;
  logic [7:0] read_data;
  logic       resp;

  clocking master_cb @(posedge clk);
    output  req;
    input   ack;
    output  is_write;
    output  address;
    output  write_data;
    input   read_data;
    input   resp;
  endclocking

  clocking slave_cb @(posedge clk);
    input   req;
    output  ack;
    input   is_write;
    input   address;
    input   write_data;
    output  read_data;
    output  resp;
  endclocking

  clocking monitor_cb @(posedge clk);
    input req;
    input ack;
    input is_write;
    input address;
    input write_data;
    input read_data;
    input resp;
  endclocking
endinterface

interface sample_clock_reset_if();
  timeunit      1ns;
  timeprecision 1ps;

  bit       clk         = 0;
  realtime  half_period = 0.0;
  event     clk_started;
  bit       rst_n       = 1;

  task start_clock(realtime period_ns);
    half_period = period_ns / 2.0;
    ->clk_started;
  endtask

  task initiate_reset(realtime duration_ns);
    rst_n = 0;
    #(duration_ns);
    rst_n = 1;
  endtask

  always @(clk_started) begin
    forever #(half_period) begin
      clk ^= 1;
    end
  end
endinterface

package sample_pkg;
  timeunit  1ns;

  import  uvm_pkg::*;
  import  tue_pkg::*;

  `include  "uvm_macros.svh"
  `include  "tue_macros.svh"

  typedef virtual sample_bus_if         sample_bus_vif;
  typedef virtual sample_clock_reset_if sample_clock_reset_vif;

  class sample_configuration extends tue_configuration;
    sample_bus_vif  vif;
    `tue_object_default_constructor(sample_configuration)
    `uvm_object_utils(sample_configuration)
  endclass

  class sample_item extends tue_sequence_item #(sample_configuration);
    rand  bit       is_write;
    rand  bit [2:0] address;
    rand  bit [7:0] data;
    rand  bit       resp;

    `tue_object_default_constructor(sample_item)
    `uvm_object_utils_begin(sample_item)
      `uvm_field_int(is_write, UVM_DEFAULT | UVM_BIN)
      `uvm_field_int(address , UVM_DEFAULT | UVM_HEX)
      `uvm_field_int(data    , UVM_DEFAULT | UVM_HEX)
      `uvm_field_int(resp    , UVM_DEFAULT | UVM_BIN)
    `uvm_object_utils_end
  endclass

  class sample_master_driver extends tue_driver #(.CONFIGURATION(sample_configuration), .REQ(sample_item));
    sample_bus_vif  vif;

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      vif = configuration.vif;
    endfunction

    task run_phase(uvm_phase phase);
      fork
        forever @(negedge vif.rst_n) begin
          do_reset();
        end
        forever begin
          execute_item();
        end
      join_none
    endtask

    task do_reset();
      vif.req         = 0;
      vif.is_write    = 0;
      vif.address     = 0;
      vif.write_data  = 0;
    endtask

    task execute_item();
      sample_item item;

      seq_item_port.get_next_item(item);
      @(vif.master_cb);

      vif.master_cb.req         <= 1;
      vif.master_cb.is_write    <= item.is_write;
      vif.master_cb.address     <= item.address;
      vif.master_cb.write_data  <= item.data;

      do begin
        @(vif.master_cb);
      end while (!vif.master_cb.ack);

      item.resp = vif.master_cb.resp;
      if (!item.is_write) begin
        item.data = vif.master_cb.read_data;
      end

      vif.master_cb.req         <= 0;
      vif.master_cb.is_write    <= 0;
      vif.master_cb.address     <= 0;
      vif.master_cb.write_data  <= 0;

      seq_item_port.item_done();
    endtask

    `tue_component_default_constructor(sample_master_driver)
    `uvm_component_utils(sample_master_driver)
  endclass

  class sample_master_monitor extends tue_param_monitor #(.CONFIGURATION(sample_configuration), .ITEM(sample_item));
    sample_bus_vif  vif;

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      vif = configuration.vif;
    endfunction

    task run_phase(uvm_phase phase);
      sample_item item;
      forever @(vif.monitor_cb) begin
        if ((item == null) && vif.monitor_cb.req) begin
          item          = create_item("master_item");
          item.is_write = vif.monitor_cb.is_write;
          item.address  = vif.monitor_cb.address;
          item.data     = vif.monitor_cb.write_data;
        end
        else if (vif.monitor_cb.ack) begin
          item.resp = vif.monitor_cb.resp;
          if (!item.is_write) begin
            item.data = vif.monitor_cb.read_data;
          end
          write_item(item);
          item  = null;
        end
      end
    endtask

    `tue_component_default_constructor(sample_master_monitor)
    `uvm_component_utils(sample_master_monitor)
  endclass

  typedef tue_sequencer #(.CONFIGURATION(sample_configuration), .REQ(sample_item))  sample_master_sequencer;

  class sample_master_agent extends tue_param_agent #(
    .CONFIGURATION  (sample_configuration   ),
    .ITEM           (sample_item            ),
    .MONITOR        (sample_master_monitor  ),
    .SEQUENCER      (sample_master_sequencer),
    .DRIVER         (sample_master_driver   )
  );
    `tue_component_default_constructor(sample_master_agent)
    `uvm_component_utils(sample_master_agent)
  endclass

  class sample_slave_driver extends tue_driver #(.CONFIGURATION(sample_configuration), .REQ(sample_item));
    sample_bus_vif  vif;

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      vif = configuration.vif;
    endfunction

    task run_phase(uvm_phase phase);
      fork
        forever @(negedge vif.rst_n) begin
          do_reset();
        end
        forever begin
          execute_item();
        end
      join_none
    endtask

    task do_reset();
      vif.ack         = 0;
      vif.resp        = 0;
      vif.read_data   = 0;
    endtask

    task execute_item();
      sample_item item;

      seq_item_port.get_next_item(item);

      vif.slave_cb.ack  <= 1;
      vif.slave_cb.resp <= item.resp;
      if (!vif.slave_cb.is_write) begin
        vif.slave_cb.read_data   <= item.data;
      end

      @(vif.slave_cb);

      vif.slave_cb.ack        <= 0;
      vif.slave_cb.resp       <= 0;
      vif.slave_cb.read_data  <= 0;

      seq_item_port.item_done();
    endtask

    `tue_component_default_constructor(sample_slave_driver)
    `uvm_component_utils(sample_slave_driver)
  endclass

  class sample_slave_monitor extends tue_reactive_monitor #(.CONFIGURATION(sample_configuration), .ITEM(sample_item));
    sample_bus_vif  vif;

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      vif = configuration.vif;
    endfunction

    task run_phase(uvm_phase phase);
      sample_item item;
      forever @(vif.monitor_cb) begin
        if ((item == null) && vif.monitor_cb.req) begin
          item          = create_item("master_item");
          item.is_write = vif.monitor_cb.is_write;
          item.address  = vif.monitor_cb.address;
          item.data     = vif.monitor_cb.write_data;
          write_request(item.clone());
        end
        else if (vif.monitor_cb.ack) begin
          item.resp = vif.monitor_cb.resp;
          if (!item.is_write) begin
            item.data = vif.monitor_cb.read_data;
          end
          write_item(item);
          item  = null;
        end
      end
    endtask

    `tue_component_default_constructor(sample_slave_monitor)
    `uvm_component_utils(sample_slave_monitor)
  endclass

  typedef tue_reactive_fifo_sequencer #(.CONFIGURATION(sample_configuration), .ITEM(sample_item))  sample_slave_sequencer;

  class sample_slave_agent extends tue_reactive_agent #(
    .CONFIGURATION  (sample_configuration   ),
    .ITEM           (sample_item            ),
    .MONITOR        (sample_slave_monitor   ),
    .SEQUENCER      (sample_slave_sequencer ),
    .DRIVER         (sample_slave_driver    )
  );
    `tue_component_default_constructor(sample_slave_agent)
    `uvm_component_utils(sample_slave_agent)
  endclass

  class sample_master_sequence extends tue_sequence #(.CONFIGURATION(sample_configuration), .REQ(sample_item));
    function new(string name = "sample_master_sequence");
      super.new(name);
      set_automatic_phase_objection(1);
    endfunction

    task body();
      sample_item item;
      repeat (4) begin
        `uvm_do_with(item, { is_write == 1; })
      end
      repeat (4) begin
        `uvm_do_with(item, { is_write == 0; })
      end
    endtask

    `uvm_object_utils(sample_master_sequence)
  endclass

  class sample_slave_sequence extends tue_reactive_sequence #(.CONFIGURATION(sample_configuration), .ITEM(sample_item));
    bit [7:0] data[bit [2:0]];

    function new(string name = "sample_slave_sequence");
      super.new(name);
      set_automatic_phase_objection(0);
    endfunction

    task body();
      sample_item request;
      sample_item item;
      forever begin
        get_request(request);
        if (request.is_write) begin
          data[request.address] = request.data;
          `uvm_do_with(item, { resp == 0; })
        end
        else if (data.exists(request.address)) begin
          bit [7:0] read_data = data[request.address];
          `uvm_do_with(item, { resp == 0; data == read_data; });
        end
        else begin
          `uvm_do_with(item, { resp == 1; })
        end
      end
    endtask

    `uvm_object_utils(sample_slave_sequence)
  endclass

  class sample_test extends tue_test #(sample_configuration);
    sample_master_agent master_agent;
    sample_slave_agent  slave_agent;

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      master_agent  = sample_master_agent::type_id::create("master_agent", this);
      master_agent.set_context(configuration, status);

      slave_agent   = sample_slave_agent::type_id::create("sample_agent", this);
      slave_agent.set_context(configuration, status);
    endfunction

    function void connect_phase(uvm_phase phase);
      uvm_config_db #(uvm_object_wrapper)::set(master_agent.sequencer, "main_phase", "default_sequence", sample_master_sequence::type_id::get());
      uvm_config_db #(uvm_object_wrapper)::set(slave_agent.sequencer , "main_phase", "default_sequence", sample_slave_sequence::type_id::get());
    endfunction

    task reset_phase(uvm_phase phase);
      sample_clock_reset_vif  clock_reset_vif;
      phase.raise_objection(this);
      void'(uvm_config_db #(sample_clock_reset_vif)::get(null, "", "clock_reset_vif", clock_reset_vif));
      clock_reset_vif.start_clock(100ns);
      clock_reset_vif.initiate_reset(1us);
      phase.drop_objection(this);
    endtask

    function void create_configuration();
      super.create_configuration();
      void'(uvm_config_db #(sample_bus_vif)::get(null, "", "bus_vif", configuration.vif));
    endfunction

    `tue_component_default_constructor(sample_test)
    `uvm_component_utils(sample_test)
  endclass
endpackage

module top();
  import  uvm_pkg::*;
  import  sample_pkg::*;

  sample_clock_reset_if clock_reset_if();
  initial begin
    uvm_config_db #(sample_clock_reset_vif)::set(null, "", "clock_reset_vif", clock_reset_if);
  end

  sample_bus_if bus_if (
    .clk    (clock_reset_if.clk   ),
    .rst_n  (clock_reset_if.rst_n )
  );
  initial begin
    uvm_config_db #(sample_bus_vif)::set(null, "", "bus_vif", bus_if);
  end

  initial begin
    run_test("sample_test");
  end
endmodule