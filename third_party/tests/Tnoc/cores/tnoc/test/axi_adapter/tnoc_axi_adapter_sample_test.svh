`ifndef TNOC_AXI_ADAPTER_SAMPLE_TEST_SVH
`define TNOC_AXI_ADAPTER_SAMPLE_TEST_SVH
class tnoc_axi_adapter_sample_test_sequence extends tnoc_axi_adapter_test_sequence_base;
  tvip_axi_address  address_mask[int];

  task body();
    foreach (p_sequencer.axi_master_sequencer[i, j]) begin
      fork
        automatic int ii  = i;
        automatic int jj  = j;
        do_access(p_sequencer.axi_master_sequencer[ii][jj]);
      join_none
    end
    wait fork;
  endtask

  task do_access(tvip_axi_master_sequencer sequencer);
    for (int i = 0;i < 3;++i) begin
      for (int j = 0;j < 16;++j) begin
        do_write_read_access(sequencer, i, j);
      end
    end
  endtask

  task do_write_read_access(
    tvip_axi_master_sequencer sequencer,
    int                       slave_index,
    int                       address_index
  );
    tvip_axi_configuration          axi_cfg;
    tvip_axi_address                address_range;
    tvip_axi_address                begin_address;
    tvip_axi_address                end_address;
    tvip_axi_master_write_sequence  write_sequence;
    tvip_axi_master_read_sequence   read_sequence;

    axi_cfg       = sequencer.get_configuration();
    address_range = (2**(axi_cfg.address_width - 6));
    begin_address = (2**(axi_cfg.address_width - 2)) * slave_index + address_range * (address_index + 0) - 0;
    end_address   = (2**(axi_cfg.address_width - 2)) * slave_index + address_range * (address_index + 1) - 1;

    `uvm_do_on_with(write_sequence, sequencer, {
      address inside {[begin_address:end_address]};
      (address + burst_size * burst_length) <= end_address;
    })
    `uvm_do_on_with(read_sequence, sequencer, {
      address      == write_sequence.address;
      burst_size   == write_sequence.burst_size;
      burst_length == write_sequence.burst_length;
    })

    if (!compare_result(axi_cfg, write_sequence, read_sequence)) begin
      `uvm_error("CMPDATA", "write and read data are mismatched !!")
    end
  endtask

  function bit compare_result(
    tvip_axi_configuration          axi_cfg,
    tvip_axi_master_write_sequence  write_sequence,
    tvip_axi_master_read_sequence   read_sequence
  );
    tvip_axi_address  address;
    int               burst_size;
    int               byte_width;

    address     = write_sequence.address;
    burst_size  = write_sequence.burst_size;
    byte_width  = axi_cfg.data_width / 8;
    foreach (write_sequence.data[i]) begin
      int start_byte  = ((address & get_address_mask(burst_size)) + (burst_size * i)) % byte_width;
      for (int j = 0;j < burst_size;++j) begin
        byte  write_byte;
        byte  read_byte;

        if (!write_sequence.strobe[i][start_byte+j]) begin
          continue;
        end

        write_byte  = write_sequence.data[i][8*(start_byte+j)+:8];
        read_byte   = read_sequence.data[i][8*(start_byte+j)+:8];
        if (write_byte != read_byte) begin
          return 0;
        end
      end
    end

    return 1;
  endfunction

  function tvip_axi_address get_address_mask(int burst_size);
    if (!address_mask.exists(burst_size)) begin
      tvip_axi_address  mask;
      mask                      = '1;
      mask                      = (mask >> $clog2(burst_size)) << $clog2(burst_size);
      address_mask[burst_size]  = mask;
    end
    return address_mask[burst_size];
  endfunction

  `tue_object_default_constructor(tnoc_axi_adapter_sample_test_sequence)
  `uvm_object_utils(tnoc_axi_adapter_sample_test_sequence)
endclass

class tnoc_axi_adapter_sample_test extends tnoc_axi_adapter_test_base;
  function void start_of_simulation_phase(uvm_phase phase);
    super.start_of_simulation_phase(phase);
    set_default_sequence(sequencer, "main_phase", tnoc_axi_adapter_sample_test_sequence::type_id::get());
  endfunction
  `tue_component_default_constructor(tnoc_axi_adapter_sample_test)
  `uvm_component_utils(tnoc_axi_adapter_sample_test)
endclass
`endif
