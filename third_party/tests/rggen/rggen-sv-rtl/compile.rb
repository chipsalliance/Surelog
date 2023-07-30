if macro_defined? :RGGEN_ENABLE_BACKDOOR
  file_list 'compile_backdoor.rb', from: :current
end

[
  'rggen_rtl_pkg.sv',
  'rggen_or_reducer.sv',
  'rggen_mux.sv',
  'rggen_bit_field_if.sv',
  'rggen_bit_field.sv',
  'rggen_bit_field_w01trg.sv',
  'rggen_register_if.sv',
  'rggen_address_decoder.sv',
  'rggen_register_common.sv',
  'rggen_default_register.sv',
  'rggen_external_register.sv',
  'rggen_indirect_register.sv',
  'rggen_bus_if.sv',
  'rggen_adapter_common.sv',
  'rggen_apb_if.sv',
  'rggen_apb_adapter.sv',
  'rggen_apb_bridge.sv',
  'rggen_axi4lite_if.sv',
  'rggen_axi4lite_skid_buffer.sv',
  'rggen_axi4lite_adapter.sv',
  'rggen_axi4lite_bridge.sv',
  'rggen_wishbone_if.sv',
  'rggen_wishbone_adapter.sv',
  'rggen_wishbone_bridge.sv'
].each { |file| source_file file }
