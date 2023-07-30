`ifndef RGGEN_BACKDOOR_IF_SV
`define RGGEN_BACKDOOR_IF_SV

`ifdef RGGEN_ENABLE_BACKDOOR

`ifndef RGGEN_BACKDOOR_DATA_WIDTH
  `ifdef UVM_REG_DATA_WIDTH
    `define RGGEN_BACKDOOR_DATA_WIDTH `UVM_REG_DATA_WIDTH
  `else
    `define RGGEN_BACKDOOR_DATA_WIDTH 64
  `endif
`endif

interface rggen_backdoor_if(
  input logic i_clk,
  input logic i_rst_n
);
  typedef bit [`RGGEN_BACKDOOR_DATA_WIDTH-1:0]  rggen_backdoor_data;

  bit                 valid;
  rggen_backdoor_data read_mask;
  rggen_backdoor_data write_mask;
  rggen_backdoor_data write_data;
  rggen_backdoor_data read_data;
  rggen_backdoor_data value;

  clocking backdoor_cb @(posedge i_clk);
    output  valid;
    output  read_mask;
    output  write_mask;
    output  write_data;
    input   read_data;
    input   value;
  endclocking

  event at_clock_edge;
  always @(backdoor_cb) begin
    ->at_clock_edge;
  end

  semaphore backdoor_access_lock;
  initial begin
    backdoor_access_lock  = new(1);
  end

  task automatic backdoor_read(
    input rggen_backdoor_data mask,
    ref   rggen_backdoor_data data
  );
    backdoor_access(0, mask, data);
  endtask

  task automatic backdoor_write(
    rggen_backdoor_data mask,
    rggen_backdoor_data data
  );
    backdoor_access(1, mask, data);
  endtask

  task automatic backdoor_access(
    input bit                 write,
    input rggen_backdoor_data mask,
    ref   rggen_backdoor_data data
  );
    backdoor_access_lock.get(1);

    if (!at_clock_edge.triggered) begin
      @(backdoor_cb);
    end

    backdoor_cb.valid <= '1;
    if (write) begin
      backdoor_cb.read_mask   <= '0;
      backdoor_cb.write_mask  <= mask;
      backdoor_cb.write_data  <= data;
    end
    else begin
      data  = get_read_data();
      backdoor_cb.read_mask   <= mask;
      backdoor_cb.write_mask  <= '0;
    end

    @(backdoor_cb);
    backdoor_cb.valid <= '0;

    backdoor_access_lock.put(1);
  endtask

  function automatic rggen_backdoor_data get_read_data();
    return backdoor_cb.read_data;
  endfunction

  function automatic rggen_backdoor_data get_value();
    return backdoor_cb.value;
  endfunction

  task automatic wait_for_change();
    @(backdoor_cb.read_data);
  endtask
endinterface
`endif

`endif
