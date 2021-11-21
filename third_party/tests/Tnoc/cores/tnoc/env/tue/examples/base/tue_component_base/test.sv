package sample_pkg;
  import  uvm_pkg::*;
  import  tue_pkg::*;

  `include "uvm_macros.svh"
  `include "tue_macros.svh"

  class sample_configuration extends tue_configuration;
    `tue_object_default_constructor(sample_configuration)
    `uvm_object_utils(sample_configuration)
  endclass

  class sample_status extends tue_status;
    `tue_object_default_constructor(sample_status)
    `uvm_object_utils(sample_status)
  endclass

  class sample_component_a extends tue_component#(.CONFIGURATION(sample_configuration));
    `tue_component_default_constructor(sample_component_a)
    `uvm_component_utils(sample_component_a)
  endclass

  class sample_component_b extends tue_component#(.STATUS(sample_status));
    `tue_component_default_constructor(sample_component_b)
    `uvm_component_utils(sample_component_b)
  endclass

  class sample_test extends tue_test #(sample_configuration, sample_status);
    sample_component_a    a0;
    sample_component_a    a1;
    sample_component_a    a2;
    sample_component_a    a3;
    sample_component_b    b0;
    sample_component_b    b1;
    sample_component_b    b2;
    sample_component_b    b3;

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      a0  = sample_component_a::type_id::create("a0", this);
      a0.set_configuration(configuration);

      a1  = sample_component_a::type_id::create("a1", this);
      uvm_config_db#(sample_configuration)::set(a1, "", "configuration", configuration);

      a2  = sample_component_a::type_id::create("a2", this);
      a2.set_report_severity_override(UVM_FATAL, UVM_WARNING);

      a3  = sample_component_a::type_id::create("a3", this);
      a3.set_report_severity_override(UVM_FATAL, UVM_WARNING);
      uvm_config_db#(sample_configuration)::set(a3, "", "configuration", null);

      b0  = sample_component_b::type_id::create("b0", this);
      b0.set_status(status);

      b1  = sample_component_b::type_id::create("b1", this);
      uvm_config_db#(sample_status)::set(b1, "", "status", status);

      b2  = sample_component_b::type_id::create("b2", this);

      b3  = sample_component_b::type_id::create("b3", this);
      uvm_config_db#(sample_status)::set(b3, "", "status", null);
    endfunction

    function void start_of_simulation_phase(uvm_phase phase);
      if ((a0.get_configuration() != configuration) || (a0.get_status() != null)) begin
        `uvm_fatal(get_name(), "Error!")
      end
      if ((a1.get_configuration() != configuration) || (a1.get_status() != null)) begin
        `uvm_fatal(get_name(), "Error!")
      end
      if ((a2.get_configuration() != null) || (a2.get_status() != null)) begin
        `uvm_fatal(get_name(), "Error!")
      end
      if ((a3.get_configuration() != null) || (a3.get_status() != null)) begin
        `uvm_fatal(get_name(), "Error!")
      end
      if ((b0.get_status() != status) || (b0.get_configuration() != null)) begin
        `uvm_fatal(get_name(), "Error!")
      end
      if ((b1.get_status() != status) || (b1.get_configuration() != null)) begin
        `uvm_fatal(get_name(), "Error!")
      end
      if ((b2.get_status() == null) || (b2.get_status() == status) || (b2.get_configuration() != null)) begin
        `uvm_fatal(get_name(), "Error!")
      end
      if ((b3.get_status() == null) || (b3.get_status() == status) || (b3.get_configuration() != null)) begin
        `uvm_fatal(get_name(), "Error!")
      end
    endfunction

    function void report_phase(uvm_phase phase);
      uvm_report_server report_server = uvm_report_server::get_server();
      if (report_server.get_severity_count(UVM_WARNING) == 2) begin
        `uvm_info(get_name(), "OK!", UVM_MEDIUM)
      end
      else begin
        `uvm_fatal(get_name(), "NG!")
      end
    endfunction

    `tue_component_default_constructor(sample_test)
    `uvm_component_utils(sample_test)
  endclass
endpackage

module top();
  import uvm_pkg::*;
  import sample_pkg::*;

  initial begin
    run_test("sample_test");
  end
endmodule
