`ifndef TNOC_MODEL_BASE_SVH
`define TNOC_MODEL_BASE_SVH
virtual class tnoc_model_base #(
  type  CONFIGURATION = tue_configuration_dummy,
  type  STATUS        = tue_status_dummy
) extends tue_component #(CONFIGURATION, STATUS);
  typedef tnoc_model_base #(
    CONFIGURATION, STATUS
  ) this_type;

  typedef uvm_analysis_port #(tnoc_bfm_packet_item)
    tue_packet_analysis_port;

  uvm_analysis_imp #(
    tnoc_bfm_packet_item, this_type
  ) packet_export;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    packet_export = new("packet_export", this);
  endfunction

  function void write(tnoc_bfm_packet_item item);
    tnoc_bfm_packet_item      expected_item;
    tue_packet_analysis_port  port;

    expected_item = create_expected_item(item);
    if (expected_item == null) begin
      return;
    end

    port  = find_port(expected_item);
    if (port == null) begin
      return;
    end
    port.write(expected_item);
  endfunction

  protected virtual function tnoc_bfm_packet_item create_expected_item(
    tnoc_bfm_packet_item  item
  );
    if (is_valid_item(item)) begin
      return item;
    end
    else if (item.is_non_posted_request()) begin
      return create_error_response_item(item);
    end
    else begin
      return null;
    end
  endfunction

  protected virtual function bit is_valid_item(
    tnoc_bfm_packet_item  item
  );
    if (item.invalid_destination) begin
      return 0;
    end
    else if (item.destination_id.x >= configuration.size_x) begin
      return 0;
    end
    else if (item.destination_id.y >= configuration.size_y) begin
      return 0;
    end
    else begin
      return 1;
    end
  endfunction

  protected virtual function tnoc_bfm_packet_item create_error_response_item(
    tnoc_bfm_packet_item  item
  );
    tnoc_bfm_packet_item  response_item;

    response_item                     = tnoc_bfm_packet_item::type_id::create(item.get_name());
    response_item.packet_type         = (item.has_payload()) ? TNOC_BFM_RESPONSE : TNOC_BFM_RESPONSE_WITH_DATA;
    response_item.destination_id      = item.source_id;
    response_item.source_id           = item.destination_id;
    response_item.vc                  = item.vc;
    response_item.tag                 = item.tag;
    response_item.invalid_destination = 0;
    if (item.has_payload()) begin
      response_item.response_status     = new[1];
      response_item.response_status[0]  = '{ decode_error: 1'b1, default: 1'b0 };
    end
    else begin
      int length  = item.get_request_burst_length();
      response_item.byte_size       = item.byte_size;
      response_item.byte_offset     = get_byte_offset(item);
      response_item.byte_end        = get_byte_end(item);
      response_item.last_response   = item.has_no_payload();
      response_item.data            = new[length];
      response_item.response_status = new[length];
      foreach (response_item.data[i]) begin
        response_item.data[i]             = configuration.error_data;
        response_item.response_status[i]  = '{ decode_error: 1'b1, default: 1'b0 };
      end
    end

    return response_item;
  endfunction

  protected pure virtual function tue_packet_analysis_port find_port(
    tnoc_bfm_packet_item  item
  );

  local function tnoc_bfm_byte_offset get_byte_offset(tnoc_bfm_packet_item item);
    tnoc_bfm_configuration  packet_configuration;
    packet_configuration  = item.get_configuration();
    return item.address % packet_configuration.max_byte_width;
  endfunction

  local function tnoc_bfm_byte_end get_byte_end(tnoc_bfm_packet_item item);
    tnoc_bfm_configuration  packet_configuration;
    packet_configuration  = item.get_configuration();
    return (item.address + (item.byte_length - 1)) % packet_configuration.byte_width;
  endfunction

  `tue_component_default_constructor(tnoc_model_base)
endclass
`endif
