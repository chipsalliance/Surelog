`ifndef TNOC_FABRIC_ENV_MODEL_SVH
`define TNOC_FABRIC_ENV_MODEL_SVH
class tnoc_fabric_env_model extends tnoc_model_base #(tnoc_fabric_env_configuration);
  tue_packet_analysis_port  packet_port[int][int];

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    for (int y = 0;y < configuration.size_y;++y) begin
      for (int x = 0;x < configuration.size_x;++x) begin
        packet_port[y][x] = new($sformatf("packet_port[%0d][%0d]", y, x), this);
      end
    end
  endfunction

  function tue_packet_analysis_port find_port(
    tnoc_bfm_packet_item  item
  );
    tnoc_bfm_location_id  id  = item.destination_id;
    return packet_port[id.y][id.x];
  endfunction
  
  `tue_component_default_constructor(tnoc_fabric_env_model)
  `uvm_component_utils(tnoc_fabric_env_model)
endclass
`endif
