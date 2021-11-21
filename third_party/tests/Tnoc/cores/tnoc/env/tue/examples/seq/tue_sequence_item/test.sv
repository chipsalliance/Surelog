package sample_pkg;
  import  uvm_pkg::*;
  import  tue_pkg::*;
  `include  "tue_macros.svh"

  class sample_configuration #(type T = bit) extends tue_configuration;
    T v;
    `tue_object_default_constructor(sample_configuration)
    `uvm_object_param_utils(sample_configuration)
  endclass

  class sample_status #(type T = bit) extends tue_status;
    T v;
    `tue_object_default_constructor(sample_status)
    `uvm_object_param_utils(sample_status)
  endclass

  class sample_item extends tue_sequence_item #(sample_configuration, sample_status);
    rand  bit [1:0] v;

    constraint c {
      v == {status.v, configuration.v};
    };

    `tue_object_default_constructor(sample_item)
    `uvm_object_utils(sample_item)
  endclass

  class sample_sequence extends tue_sequence #(sample_configuration, sample_status, sample_item);
    function new(string name = "sample_sequence");
      super.new(name);
      set_automatic_phase_objection(1);
    endfunction

    task body();
      for (int i = 0;i < 4;i++) begin
        configuration.v = i[0];
        status.v        = i[1];
        `uvm_create(req)
        if (!(req.randomize() || (req.v == i))) begin
          `uvm_fatal(get_name(), "Error!")
        end
        #1;
      end
    endtask

    `uvm_object_utils(sample_sequence)
  endclass

  typedef tue_sequencer #(sample_configuration, sample_status, sample_item) sample_sequencer;

  class sample_test extends tue_test #(sample_configuration, sample_status);
    sample_sequencer      sequencer;

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      sequencer     = sample_sequencer::type_id::create("sequencer", this);
      sequencer.set_configuration(configuration);
      sequencer.set_status(status);
    endfunction

    function void connect_phase(uvm_phase phase);
      uvm_config_db #(uvm_object_wrapper)::set(sequencer, "main_phase", "default_sequence", sample_sequence::type_id::get());
    endfunction

    `tue_component_default_constructor(sample_test)
    `uvm_component_utils(sample_test)
  endclass
endpackage

module test();
  import uvm_pkg::*;
  import sample_pkg::*;

  initial begin
    run_test("sample_test");
  end
endmodule
