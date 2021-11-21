`ifndef TNOC_ROUTER_ENV_MODEL_SVH
`define TNOC_ROUTER_ENV_MODEL_SVH
class tnoc_router_env_model extends tnoc_model_base #(tnoc_router_env_configuration);
  tue_packet_analysis_port  packet_port[5];

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    foreach (packet_port[i]) begin
      packet_port[i]  = new($sformatf("packet_port[%0d]", i), this);
    end
  endfunction

  function tue_packet_analysis_port find_port(
    tnoc_bfm_packet_item  item
  );
    bit [3:0] result;

    result[0] = (item.destination_id.x > configuration.id_x) ? '1 : '0;
    result[1] = (item.destination_id.x < configuration.id_x) ? '1 : '0;
    result[2] = (item.destination_id.y > configuration.id_y) ? '1 : '0;
    result[3] = (item.destination_id.y < configuration.id_y) ? '1 : '0;

    case (1)
      result[0]:  return  packet_port[0];
      result[1]:  return  packet_port[1];
      result[2]:  return  packet_port[2];
      result[3]:  return  packet_port[3];
      default:    return  packet_port[4];
    endcase
  endfunction

  `tue_component_default_constructor(tnoc_router_env_model)
  `uvm_component_utils(tnoc_router_env_model)
endclass
`endif
