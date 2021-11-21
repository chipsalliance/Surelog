`ifndef TNOC_BFM_FLIT_ITEM_SVH
`define TNOC_BFM_FLIT_ITEM_SVH

typedef tue_sequence_item #(
  tnoc_bfm_configuration, tnoc_bfm_status
)  tnoc_bfm_flit_item_base;

class tnoc_bfm_flit_item extends tnoc_bfm_flit_item_base;
  `uvm_object_registry(tnoc_bfm_flit_item, "tnoc_bfm_flit_item")

  rand  tnoc_bfm_flit_type  flit_type;
  rand  bit                 head;
  rand  bit                 tail;
  rand  tnoc_bfm_flit_data  data;

  static function tnoc_bfm_flit_item create_flit_item(input string name, const ref tnoc_bfm_flit flit);
    tnoc_bfm_flit_item  flit_item;
    flit_item = tnoc_bfm_flit_item::type_id::create(name);
    flit_item.set_flit(flit);
    return flit_item;
  endfunction

  static function tnoc_bfm_flit_item create_header_flit_item(string name, bit head, bit tail, tnoc_bfm_flit_data data);
    tnoc_bfm_flit_item  flit_item;
    flit_item           = tnoc_bfm_flit_item::type_id::create(name);
    flit_item.flit_type = TNOC_BFM_HEADER_FLIT;
    flit_item.head      = head;
    flit_item.tail      = tail;
    flit_item.data      = data;
    return flit_item;
  endfunction

  static function tnoc_bfm_flit_item create_payload_flit_item(string name, bit tail, tnoc_bfm_flit_data data);
    tnoc_bfm_flit_item  flit_item;
    flit_item           = tnoc_bfm_flit_item::type_id::create(name);
    flit_item.flit_type = TNOC_BFM_PAYLOAD_FLIT;
    flit_item.head      = 0;
    flit_item.tail      = tail;
    flit_item.data      = data;
    return flit_item;
  endfunction

  function bit is_header_flit();
    return (flit_type == TNOC_BFM_HEADER_FLIT);
  endfunction

  function bit is_payload_flit();
    return (flit_type == TNOC_BFM_PAYLOAD_FLIT);
  endfunction

  function bit is_head_flit();
    return head;
  endfunction

  function bit is_tail_flit();
    return tail;
  endfunction

  function void set_flit(const ref tnoc_bfm_flit flit);
    flit_type = flit.flit_type;
    head      = flit.head;
    tail      = flit.tail;
    data      = flit.data;
  endfunction

  function tnoc_bfm_flit get_flit();
    tnoc_bfm_flit flit;
    flit.flit_type  = flit_type;
    flit.head       = head;
    flit.tail       = tail;
    flit.data       = data;
    return flit;
  endfunction

  `tue_object_default_constructor(tnoc_bfm_flit_item)
  `uvm_field_utils_begin(tnoc_bfm_flit_item)
    `uvm_field_enum(tnoc_bfm_flit_type, flit_type, UVM_DEFAULT)
    `uvm_field_int(head, UVM_DEFAULT | UVM_BIN)
    `uvm_field_int(tail, UVM_DEFAULT | UVM_BIN)
    `uvm_field_int(data, UVM_DEFAULT | UVM_HEX)
  `uvm_field_utils_end
endclass

`endif
