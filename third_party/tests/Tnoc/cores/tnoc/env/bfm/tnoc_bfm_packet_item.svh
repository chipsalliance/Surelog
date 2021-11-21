`ifndef TNOC_BFM_PACKET_ITEM_SVH
`define TNOC_BFM_PACKET_ITEM_SVH
typedef tue_sequence_item #(
  tnoc_bfm_configuration, tnoc_bfm_status
) tnoc_bfm_packet_item_base;

class tnoc_bfm_packet_item extends tnoc_bfm_packet_item_base;
  rand    tnoc_bfm_packet_type      packet_type;
  rand    tnoc_bfm_location_id      destination_id;
  rand    tnoc_bfm_location_id      source_id;
  rand    int                       vc;
  rand    int                       tag;
  rand    bit                       invalid_destination;
  rand    int                       byte_size;
  rand    int                       byte_length;
  rand    tnoc_bfm_address          address;
  rand    tnoc_bfm_burst_type       burst_type;
  rand    int                       byte_offset;
  rand    int                       byte_end;
  rand    bit                       last_response;
  rand    tnoc_bfm_data             data[];
  rand    tnoc_bfm_byte_enable      byte_enable[];
  rand    tnoc_bfm_response_status  response_status[];
  rand    int                       burst_length;
          int                       tr_handle;
  static  uvm_packer                flit_packer;

  constraint c_packet_type_solve_order {
    solve packet_type before byte_size;
    solve packet_type before byte_length;
    solve packet_type before address;
    solve packet_type before burst_type;
    solve packet_type before byte_offset;
    solve packet_type before byte_end;
    solve packet_type before data;
    solve packet_type before byte_enable;
    solve packet_type before response_status;
    solve packet_type before last_response;
  }

  constraint c_valid_destination_id {
    destination_id.x inside {[0:(2**this.configuration.id_x_width)-1]};
    destination_id.y inside {[0:(2**this.configuration.id_y_width)-1]};
  }

  constraint c_valid_source_id {
    source_id.x == this.configuration.id_x;
    source_id.y == this.configuration.id_y;
  }

  constraint c_valid_vc {
    vc inside {[0:this.configuration.virtual_channels-1]};
    if (this.configuration.vc_map[packet_type] >= 0) {
      soft vc == this.configuration.vc_map[packet_type];
    }
  }

  constraint c_valid_tag {
    tag inside {[0:this.configuration.tags-1]};
  }

  constraint c_default_invalid_destination {
    soft invalid_destination == 0;
  }

  constraint c_valid_byte_size {
    if (packet_type != TNOC_BFM_RESPONSE) {
      byte_size inside {[1:this.configuration.max_byte_width]};
      $countones(byte_size) == 1;
    }
    else {
      byte_size == 0;
    }
  }

  constraint c_valid_request_byte_length {
    if (!packet_type[TNOC_BFM_RESPONSE_BIT]) {
      byte_length >= 1;
      ((address % this.configuration.max_byte_length) + byte_length) <=
        this.configuration.max_byte_length;
    }
  }

  constraint c_valid_address {
    if (!packet_type[TNOC_BFM_RESPONSE_BIT]) {
      (address >> this.configuration.address_width) == 0;
    }
    else {
      address == 0;
    }
  }

  constraint c_valid_burst_type {
    if (!packet_type[TNOC_BFM_RESPONSE_BIT]) {
      burst_type == TNOC_BFM_FIXED_BURST;
    }
  }

  constraint c_valid_bye_offset {
    if (packet_type == TNOC_BFM_RESPONSE_WITH_DATA) {
      byte_offset inside {[0:this.configuration.max_byte_width-1]};
    }
    else {
      byte_offset == 0;
    }
  }

  constraint c_valid_byte_end {
    if (packet_type == TNOC_BFM_RESPONSE_WITH_DATA) {
      byte_end inside {[0:this.configuration.data_width/8-1]};
      byte_end == ((byte_offset + (byte_length - 1)) % this.configuration.byte_width);
    }
    else {
      byte_end == 0;
    }
  }

  constraint c_valid_response_byte_length {
    if (packet_type == TNOC_BFM_RESPONSE_WITH_DATA) {
      byte_length >= 1;
      (byte_offset + byte_length) <= this.configuration.max_byte_length;
    }
    else if (packet_type == TNOC_BFM_RESPONSE) {
      byte_length == 0;
    }
  }

  constraint c_valid_data {
    data.size() inside {[0:this.configuration.max_burst_length]};
    if (packet_type[TNOC_BFM_PAYLOAD_BIT]) {
      data.size() == burst_length;
    }
    else {
      data.size() == 0;
    }
    foreach (data[i]) {
      (data[i] >> this.configuration.data_width) == 0;
    }
  }

  constraint c_valid_byte_enable {
    byte_enable.size() inside {[0:this.configuration.max_burst_length]};
    if (!packet_type[TNOC_BFM_RESPONSE_BIT]) {
      byte_enable.size() == burst_length;
    }
    else {
      byte_enable.size() == 0;
    }
    foreach (byte_enable[i]) {
      (byte_enable[i] >> this.configuration.byte_enable_width) == 0;
    }
  }

  constraint c_valid_last_response {
    if (packet_type != TNOC_BFM_RESPONSE_WITH_DATA) {
      last_response == 0;
    }
  }

  constraint c_valid_response_status {
    response_status.size() inside {[0:this.configuration.max_burst_length]};
    if (packet_type == TNOC_BFM_RESPONSE_WITH_DATA) {
      response_status.size() == burst_length;
    }
    else if (packet_type == TNOC_BFM_RESPONSE) {
      response_status.size() == 1;
    }
    else {
      response_status.size() == 0;
    }
  }

  constraint c_valid_burst_length {
    if (packet_type inside {
      TNOC_BFM_POSTED_WRITE, TNOC_BFM_NON_POSTED_WRITE
    }) {
      burst_length == (
        byte_length + (address % this.configuration.byte_width) + (this.configuration.byte_width - 1)
      ) / this.configuration.byte_width;
    }
    else if (packet_type == TNOC_BFM_RESPONSE_WITH_DATA) {
      burst_length == (
        byte_length + (byte_offset % this.configuration.byte_width) + (this.configuration.byte_width - 1)
      ) / this.configuration.byte_width;
    }
    else {
      burst_length == 0;
    }
  }

  function bit is_request();
    return is_request_packet(packet_type);
  endfunction

  function bit is_non_posted_request();
    return is_non_posted_packet(packet_type);
  endfunction

  function bit is_posted_request();
    return is_posted_request_packet(packet_type);
  endfunction

  function bit is_response();
    return is_response_packet(packet_type);
  endfunction

  function bit has_payload();
    return is_packet_with_payload(packet_type);
  endfunction

  function bit has_no_payload();
    return is_packet_without_payload(packet_type);
  endfunction

  function int get_request_burst_length();
    return calc_requst_burst_length(
      address, byte_length, configuration.byte_width
    );
  endfunction

  function void pack_flit_items(ref tnoc_bfm_flit_item flit_items[$]);
    pack_header_flit_items(flit_items);
    if (has_payload()) begin
      pack_payload_flit_items(flit_items);
    end
  endfunction

  local function void pack_header_flit_items(ref tnoc_bfm_flit_item flit_items[$]);
    uvm_packer  packer;
    int         header_width;

    packer  = get_flit_packer();
    packer.pack_field_int(packet_type        , $bits(tnoc_bfm_packet_type));
    packer.pack_field_int(destination_id.y   , configuration.id_y_width   );
    packer.pack_field_int(destination_id.x   , configuration.id_x_width   );
    packer.pack_field_int(source_id.y        , configuration.id_y_width   );
    packer.pack_field_int(source_id.x        , configuration.id_x_width   );
    packer.pack_field_int(vc                 , configuration.vc_width     );
    packer.pack_field_int(tag                , configuration.tag_width    );
    packer.pack_field_int(invalid_destination, 1                          );
    if (is_request()) begin
      header_width  = configuration.get_request_header_width();
      packer.pack_field_int(get_pakced_byte_size()  , configuration.byte_size_width  );
      packer.pack_field_int(get_packed_byte_length(), configuration.byte_length_width);
      packer.pack_field_int(address                 , configuration.address_width    );
      packer.pack_field_int(burst_type              , $bits(tnoc_bfm_burst_type)     );
    end
    else if (is_response()) begin
      header_width  = configuration.get_response_header_width();
      if (has_payload()) begin
        packer.pack_field_int(get_pakced_byte_size(), configuration.byte_size_width  );
        packer.pack_field_int(byte_offset           , configuration.byte_offset_width);
        packer.pack_field_int(0                     , $bits(tnoc_bfm_response_status));
      end
      else begin
        packer.pack_field_int(0                 , configuration.byte_size_width  );
        packer.pack_field_int(0                 , configuration.byte_offset_width );
        packer.pack_field_int(response_status[0], $bits(tnoc_bfm_response_status));
      end
    end
    packer.set_packed_size();

    while (header_width > 0) begin
      int                 unpack_size;
      tnoc_bfm_flit_item  flit_item;

      if (header_width > configuration.get_flit_width()) begin
        unpack_size = configuration.get_flit_width();
      end
      else begin
        unpack_size = header_width;
      end

      flit_item = tnoc_bfm_flit_item::create_header_flit_item(
        "flit_item", 0, 0, packer.unpack_field(unpack_size)
      );
      flit_items.push_back(flit_item);

      header_width  -= unpack_size;
    end

    flit_items[0].head  = 1;
    flit_items[$].tail  = has_no_payload();
  endfunction

  local function int get_pakced_byte_size();
    return $clog2(byte_size);
  endfunction

  local function int get_packed_byte_length();
    if (byte_length == configuration.max_byte_length) begin
      return 0;
    end
    else begin
      return byte_length;
    end
  endfunction

  local function void pack_payload_flit_items(ref tnoc_bfm_flit_item flit_items[$]);
    foreach  (data[i]) begin
      uvm_packer          packer;
      tnoc_bfm_flit_item  flit_item;

      packer  = get_flit_packer();
      if (is_request()) begin
        packer.pack_field(data[i], configuration.data_width);
        packer.pack_field_int(byte_enable[i], configuration.byte_enable_width);
      end
      else if (is_response()) begin
        packer.pack_field(data[i], configuration.data_width);
        packer.pack_field_int(response_status[i]  , $bits(tnoc_bfm_response_status));
        packer.pack_field_int(get_byte_end(i)     , configuration.byte_end_width   );
        packer.pack_field_int(get_last_response(i), 1                              );
      end
      packer.set_packed_size();

      flit_item = tnoc_bfm_flit_item::create_payload_flit_item(
        "flite_item", 0, packer.unpack_field(packer.get_packed_size())
      );
      flit_items.push_back(flit_item);
    end

    flit_items[$].tail  = 1;
  endfunction

  local function int get_byte_end(int index);
    if (index == (burst_length - 1)) begin
      return byte_end;
    end
    else begin
      return 0;
    end
  endfunction

  local function bit get_last_response(int index);
    if (index == (burst_length - 1)) begin
      return last_response;
    end
    else begin
      return 0;
    end
  endfunction

  function void unpack_flit_items(const ref tnoc_bfm_flit_item flit_items[$]);
    unpack_header_flit_items(flit_items);
    if (has_payload()) begin
      unpack_payload_flit_items(flit_items);
    end
  endfunction

  local function void unpack_header_flit_items(const ref tnoc_bfm_flit_item flit_items[$]);
    uvm_packer  packer  = get_flit_packer();

    foreach (flit_items[i]) begin
      if (flit_items[i].is_header_flit()) begin
        packer.pack_field(flit_items[i].data, configuration.get_flit_width());
      end
      else begin
        break;
      end
    end
    packer.set_packed_size();

    packet_type         = tnoc_bfm_packet_type'(packer.unpack_field_int($bits(tnoc_bfm_packet_type)));
    destination_id.y    = packer.unpack_field_int(configuration.id_y_width);
    destination_id.x    = packer.unpack_field_int(configuration.id_x_width);
    source_id.y         = packer.unpack_field_int(configuration.id_y_width);
    source_id.x         = packer.unpack_field_int(configuration.id_x_width);
    vc                  = packer.unpack_field_int(configuration.vc_width);
    tag                 = packer.unpack_field_int(configuration.tag_width);
    invalid_destination = packer.unpack_field_int(1);
    if (is_request()) begin
      byte_size   = unpack_byte_size(packer);
      byte_length = unpack_byte_length(packer);
      address     = packer.unpack_field_int(configuration.address_width);
      burst_type  = tnoc_bfm_burst_type'(packer.unpack_field_int($bits(tnoc_bfm_burst_type)));
    end
    else if (is_response()) begin
      byte_size   = unpack_byte_size(packer);
      byte_offset = packer.unpack_field_int(configuration.byte_offset_width);
      if (has_no_payload()) begin
        response_status     = new[1];
        response_status[0]  = unpack_response_status(packer);
      end
    end
  endfunction

  local function int unpack_byte_size(uvm_packer packer);
    int value = packer.unpack_field_int(configuration.byte_size_width);
    return (is_request() || has_payload()) ? 2**(value + 3) : value;
  endfunction

  local function int unpack_byte_length(uvm_packer packer);
    int value = packer.unpack_field_int(configuration.byte_length_width);
    if (value == 0) begin
      return configuration.max_byte_length;
    end
    else begin
      return value;
    end
  endfunction

  local function tnoc_bfm_response_status unpack_response_status(uvm_packer packer);
    return tnoc_bfm_response_status'(packer.unpack_field_int($bits(tnoc_bfm_response_status)));
  endfunction

  local function void unpack_payload_flit_items(const ref tnoc_bfm_flit_item flit_items[$]);
    tnoc_bfm_flit_item  payload_flit_items[$];

    payload_flit_items  = flit_items.find(flit_item) with (flit_item.is_payload_flit());

    data  = new[payload_flit_items.size()];
    if (is_request()) begin
      byte_enable = new[payload_flit_items.size()];
    end
    else begin
      response_status = new[payload_flit_items.size()];
    end

    foreach (payload_flit_items[i]) begin
      uvm_packer  packer;

      packer  = get_flit_packer();
      packer.pack_field(payload_flit_items[i].data, configuration.get_payload_width());
      packer.set_packed_size();

      data[i] = packer.unpack_field(configuration.data_width);
      if (is_request()) begin
        byte_enable[i]  = packer.unpack_field_int(configuration.byte_enable_width);
      end
      else if (is_response()) begin
        response_status[i]  = unpack_response_status(packer);
        if (payload_flit_items[i].tail) begin
          byte_end      = packer.unpack_field_int(configuration.byte_end_width);
          last_response = packer.unpack_field_int(1);
        end
      end
    end
  endfunction

  local function uvm_packer get_flit_packer();
    if (flit_packer == null) begin
      flit_packer             = new();
      flit_packer.big_endian  = 0;
    end
    flit_packer.reset();
    return flit_packer;
  endfunction

  `tue_object_default_constructor(tnoc_bfm_packet_item)
  `uvm_object_utils_begin(tnoc_bfm_packet_item)
    `uvm_field_enum(tnoc_bfm_packet_type, packet_type, UVM_DEFAULT | UVM_ENUM)
    `uvm_field_int(destination_id, UVM_DEFAULT | UVM_HEX)
    `uvm_field_int(source_id, UVM_DEFAULT | UVM_HEX)
    `uvm_field_int(vc, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(tag, UVM_DEFAULT | UVM_HEX)
    `uvm_field_int(byte_size, UVM_DEFAULT | UVM_HEX)
    `uvm_field_int(byte_length, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(address, UVM_DEFAULT | UVM_HEX)
    `uvm_field_enum(tnoc_bfm_burst_type, burst_type, UVM_DEFAULT | UVM_ENUM)
    `uvm_field_int(byte_offset, UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(byte_end, UVM_DEFAULT | UVM_HEX)
    `uvm_field_int(last_response, UVM_DEFAULT | UVM_BIN)
    `uvm_field_array_int(data, UVM_DEFAULT | UVM_HEX)
    `uvm_field_array_int(byte_enable, UVM_DEFAULT | UVM_HEX)
    `uvm_field_array_int(response_status, UVM_DEFAULT | UVM_BIN)
    `uvm_field_int(burst_length, UVM_DEFAULT | UVM_DEC | UVM_NOCOMPARE)
  `uvm_object_utils_end
endclass
`endif
