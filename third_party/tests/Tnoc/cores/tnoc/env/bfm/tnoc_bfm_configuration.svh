`ifndef TNOC_BFM_CONFIGURATION_SVH
`define TNOC_BFM_CONFIGURATION_SVH
class tnoc_bfm_configuration extends tue_configuration;
  rand  uvm_active_passive_enum agent_mode;
  rand  int                     id_x_width;
  rand  int                     id_y_width;
  rand  int                     id_width;
  rand  int                     virtual_channels;
  rand  int                     vc_width;
  rand  int                     tags;
  rand  int                     tag_width;
  rand  int                     address_width;
  rand  int                     data_width;
        int                     byte_width;
        int                     byte_enable_width;
  rand  int                     max_byte_length;
        int                     byte_length_width;
        int                     max_burst_length;
  rand  int                     max_data_width;
        int                     max_byte_width;
        int                     byte_size_width;
        int                     byte_offset_width;
        int                     byte_end_width;
  rand  int                     id_x;
  rand  int                     id_y;
  rand  int                     vc_map[tnoc_bfm_packet_type];
        tnoc_bfm_flit_vif       tx_vif[int];
        tnoc_bfm_flit_vif       rx_vif[int];
  local int                     common_header_width;
  local int                     request_header_width;
  local int                     response_header_width;
  local int                     header_width;
  local int                     request_payload_width;
  local int                     response_payload_width;
  local int                     payload_width;
  local int                     flit_width;

  constraint c_default_agent_mode {
    soft agent_mode == UVM_ACTIVE;
  }

  constraint c_valid_id_width {
    id_x_width inside {[1:`TNOC_BFM_MAX_ID_X_WIDTH]};
    id_y_width inside {[1:`TNOC_BFM_MAX_ID_Y_WIDTH]};
    id_width == (id_x_width + id_y_width);
  }

  constraint c_valid_virtual_channels {
    virtual_channels inside {[1:`TNOC_BFM_MAX_VIRTUAL_CHANNELS]};
    if (virtual_channels == 1) {
      vc_width == 1;
    }
    else {
      vc_width == $clog2(virtual_channels);
    }
  }

  constraint c_valid_tags {
    tags inside {[1:`TNOC_BFM_MAX_TAGS]};
    if (tags == 1) {
      tag_width == 1;
    }
    else {
      tag_width == $clog2(tags);
    }
  }

  constraint c_valid_address_width {
    address_width inside {[1:`TNOC_BFM_MAX_ADDRESS_WIDTH]};
  }

  constraint c_valid_data_width {
    data_width inside {[8:max_data_width]};
    $countones(data_width) == 1;
  }

  constraint c_valid_max_byte_length {
    max_byte_length inside {[1:`TNOC_BFM_MAX_BYTE_LENGTH]};
    $countones(max_byte_length) == 1;
  }

  constraint c_valid_id {
    solve id_x_width before id_x;
    solve id_y_width before id_y;
    id_x inside {[0:(2**id_x_width)-1]};
    id_y inside {[0:(2**id_y_width)-1]};
  }

  constraint c_valid_vc_map {
    solve virtual_channels before vc_map;
    foreach (vc_map[packet_type]) {
      vc_map[packet_type] inside {[0:virtual_channels-1]};
    }
  }

  function new(string name = "tnoc_bfm_configuration");
    super.new(name);
    begin
      tnoc_bfm_packet_type  packet_type;
      packet_type = packet_type.first();
      for (int i = 0;i < packet_type.num();++i) begin
        vc_map[packet_type] = 0;
        packet_type = packet_type.next();
      end
    end
  endfunction

  function void post_randomize();
    super.post_randomize();
    byte_length_width = (max_byte_length == 1) ? 1 : $clog2(max_byte_length);
    byte_width        = data_width / 8;
    byte_enable_width = data_width / 8;
    max_byte_width    = max_data_width / 8;
    byte_size_width   = (max_byte_width == 1) ? 1 : $clog2($clog2(max_byte_width) + 1);
    byte_offset_width = (max_byte_width == 1) ? 1 : $clog2(max_byte_width);
    byte_end_width    = (byte_width     == 1) ? 1 : $clog2(byte_width);
    max_burst_length  = max_byte_length / byte_width;
  endfunction

  function int get_common_header_width();
    if (common_header_width == 0) begin
      common_header_width =
        $bits(tnoc_bfm_packet_type) + //  packet type
        id_width                    + //  destination id
        id_width                    + //  source id
        vc_width                    + //  virtual channel
        tag_width                   + //  tag
        1;                            //  invalid destination
    end
    return common_header_width;
  endfunction

  function int get_request_header_width();
    if (request_header_width == 0) begin
      request_header_width  =
        get_common_header_width()  +
        byte_size_width            +  //  byte size
        address_width              +  //  address
        byte_length_width          +  //  byte length
        $bits(tnoc_bfm_burst_type);   //  burst type
    end
    return request_header_width;
  endfunction

  function int get_response_header_width();
    if (response_header_width == 0) begin
      response_header_width =
        get_common_header_width() +
        byte_size_width           +       //  byte size
        byte_offset_width         +       //  byte offset
        $bits(tnoc_bfm_response_status);  //  status
    end
    return response_header_width;
  endfunction

  function int get_header_width();
    if (header_width == 0) begin
      if (get_request_header_width() > get_response_header_width()) begin
        header_width  = get_request_header_width();
      end
      else begin
        header_width  = get_response_header_width();
      end
    end
    return header_width;
  endfunction

  function int get_request_payload_width();
    if (request_payload_width == 0) begin
      request_payload_width =
        data_width +        //  data
        byte_enable_width;  //  byte enable
    end
    return request_payload_width;
  endfunction

  function int get_response_payload_width();
    if (response_payload_width == 0) begin
      response_payload_width  =
        data_width                      + //  data
        $bits(tnoc_bfm_response_status) + //  status
        byte_end_width                  + //  byte end
        1;                                //  last
    end
    return response_payload_width;
  endfunction

  function int get_payload_width();
    if (payload_width == 0) begin
      if (get_request_payload_width() > get_response_payload_width()) begin
        payload_width = get_request_payload_width();
      end
      else begin
        payload_width = get_response_payload_width();
      end
    end
    return payload_width;
  endfunction

  function int get_flit_width();
    if (flit_width == 0) begin
      if (get_common_header_width() > get_payload_width()) begin
        flit_width  = get_common_header_width();
      end
      else begin
        flit_width  = get_payload_width();
      end
    end
    return flit_width;
  endfunction

  `uvm_object_utils_begin(tnoc_bfm_configuration)
    `uvm_field_enum(uvm_active_passive_enum, agent_mode, UVM_DEFAULT | UVM_ENUM)
    `uvm_field_int(id_x_width, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(id_y_width, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(id_width, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(virtual_channels, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(vc_width, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(tags, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(tag_width, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(address_width, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(data_width, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(byte_enable_width, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(max_byte_length, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(byte_length_width, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(max_burst_length, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(max_data_width, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(max_byte_width, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(byte_size_width, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(byte_offset_width, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(byte_end_width, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(id_x, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(id_y, UVM_DEFAULT | UVM_DEC)
    `uvm_field_aa_int_enumkey(tnoc_bfm_packet_type, vc_map, UVM_DEFAULT | UVM_DEC)
  `uvm_object_utils_end
endclass
`endif
