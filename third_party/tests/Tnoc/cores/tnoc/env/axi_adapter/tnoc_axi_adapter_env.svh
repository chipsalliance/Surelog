`ifndef TNOC_AXI_ADAPTER_ENV_SVH
`define TNOC_AXI_ADAPTER_ENV_SVH
class tnoc_axi_adapter_env extends tue_env #(tnoc_axi_adapter_env_configuration);
  tvip_axi_master_agent           axi_master_agent[int][int];
  tvip_axi_slave_agent            axi_slave_agent[int][int];
  tnoc_axi_adapter_env_sequencer  sequencer;
  tnoc_fabric_env                 fabric_env;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    for (int y = 0;y < configuration.size_y;++y) begin
      for (int x = 0;x < configuration.size_x;++x) begin
        tvip_axi_configuration  axi_cfg;

        axi_cfg = configuration.get_axi_master_cfg(y, x);
        if (axi_cfg != null) begin
          axi_master_agent[y][x]  = tvip_axi_master_agent::type_id::create($sformatf("axi_master_agent[%0d][%0d]", y, x), this);
          axi_master_agent[y][x].set_configuration(axi_cfg);
          continue;
        end

        axi_cfg = configuration.get_axi_slave_cfg(y, x);
        if (axi_cfg != null) begin
          axi_slave_agent[y][x] = tvip_axi_slave_agent::type_id::create($sformatf("axi_slave_agent[%0d][%0d]", y, x), this);
          axi_slave_agent[y][x].set_configuration(axi_cfg);
        end
      end
    end

    sequencer = tnoc_axi_adapter_env_sequencer::type_id::create("sequencer", this);
    sequencer.set_configuration(configuration);

    fabric_env  = tnoc_fabric_env::type_id::create("fabric_env", this);
    fabric_env.set_configuration(configuration.fabric_env_cfg);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    foreach (axi_master_agent[y, x]) begin
      sequencer.axi_master_sequencer[y][x]  = axi_master_agent[y][x].sequencer;
    end
    foreach (axi_slave_agent[y, x]) begin
      sequencer.axi_slave_sequencer[y][x] = axi_slave_agent[y][x].sequencer;
    end
  endfunction

  `tue_component_default_constructor(tnoc_axi_adapter_env)
  `uvm_component_utils(tnoc_axi_adapter_env)
endclass
`endif
