`ifndef rggen_connect_bit_field_if
  `define rggen_connect_bit_field_if(RIF, FIF, LSB, WIDTH) \
  assign  FIF.valid                 = RIF.valid; \
  assign  FIF.read_mask             = RIF.read_mask[LSB+:WIDTH]; \
  assign  FIF.write_mask            = RIF.write_mask[LSB+:WIDTH]; \
  assign  FIF.write_data            = RIF.write_data[LSB+:WIDTH]; \
  assign  RIF.read_data[LSB+:WIDTH] = FIF.read_data; \
  assign  RIF.value[LSB+:WIDTH]     = FIF.value;
`endif
`ifndef rggen_tie_off_unused_signals
  `define rggen_tie_off_unused_signals(WIDTH, VALID_BITS, RIF) \
  if (1) begin : __g_tie_off \
    genvar  __i; \
    for (__i = 0;__i < WIDTH;++__i) begin : g \
      if ((((VALID_BITS) >> __i) % 2) == 0) begin : g \
        assign  RIF.read_data[__i]  = 1'b0; \
        assign  RIF.value[__i]      = 1'b0; \
      end \
    end \
  end
`endif
module uart_csr
  import rggen_rtl_pkg::*;
#(
  parameter int ADDRESS_WIDTH = 5,
  parameter bit PRE_DECODE = 0,
  parameter bit [ADDRESS_WIDTH-1:0] BASE_ADDRESS = '0,
  parameter bit ERROR_STATUS = 0,
  parameter bit [31:0] DEFAULT_READ_DATA = '0,
  parameter bit INSERT_SLICER = 0,
  parameter bit [7:0] DLL_INITIAL_VALUE = 8'h00,
  parameter bit [7:0] DLM_INITIAL_VALUE = 8'h00
)(
  input logic i_clk,
  input logic i_rst_n,
  rggen_apb_if.slave apb_if,
  input logic [7:0] i_rbr,
  output logic o_rbr_read_trigger,
  output logic [7:0] o_thr,
  output logic o_thr_write_trigger,
  output logic o_ier_erbfi,
  output logic o_ier_etbei,
  output logic o_ier_elsi,
  output logic o_ier_edssi,
  input logic i_iir_intpend,
  input logic [2:0] i_iir_intid2,
  output logic o_fcr_fifoen,
  output logic o_fcr_rcvr_fifo_reset_trigger,
  output logic o_fcr_xmit_fifo_reset_trigger,
  output logic o_fcr_dma_mode_select,
  output logic [1:0] o_fcr_rcvr_fifo_trigger_level,
  output logic [1:0] o_lcr_wls,
  output logic o_lcr_stb,
  output logic o_lcr_pen,
  output logic o_lcr_eps,
  output logic o_lcr_stick_parity,
  output logic o_lcr_set_break,
  output logic o_lcr_dlab,
  output logic o_mrc_dtr,
  output logic o_mrc_rts,
  output logic o_mrc_out1,
  output logic o_mrc_out2,
  output logic o_mrc_loop,
  input logic i_lsr_dr,
  input logic i_lsr_oe,
  output logic o_lsr_oe_read_trigger,
  input logic i_lsr_pe,
  output logic o_lsr_pe_read_trigger,
  input logic i_lsr_fe,
  output logic o_lsr_fe_read_trigger,
  input logic i_lsr_bi,
  output logic o_lsr_bi_read_trigger,
  input logic i_lsr_thre,
  input logic i_lsr_temt,
  input logic i_lsr_error_in_rcvr_fifo,
  input logic i_msr_dcts,
  output logic o_msr_dcts_read_trigger,
  input logic i_msr_ddsr,
  output logic o_msr_ddsr_read_trigger,
  input logic i_msr_teri,
  input logic i_msr_ddcd,
  output logic o_msr_ddcd_read_trigger,
  input logic i_msr_cts,
  input logic i_msr_dsr,
  input logic i_msr_ri,
  input logic i_msr_dcd,
  output logic [7:0] o_scratch,
  output logic [7:0] o_dll,
  output logic [7:0] o_dlm
);
  rggen_register_if #(5, 32, 32) register_if[12]();
  rggen_apb_adapter #(
    .ADDRESS_WIDTH        (ADDRESS_WIDTH),
    .LOCAL_ADDRESS_WIDTH  (5),
    .BUS_WIDTH            (32),
    .REGISTERS            (12),
    .PRE_DECODE           (PRE_DECODE),
    .BASE_ADDRESS         (BASE_ADDRESS),
    .BYTE_SIZE            (32),
    .ERROR_STATUS         (ERROR_STATUS),
    .DEFAULT_READ_DATA    (DEFAULT_READ_DATA),
    .INSERT_SLICER        (INSERT_SLICER)
  ) u_adapter (
    .i_clk        (i_clk),
    .i_rst_n      (i_rst_n),
    .apb_if       (apb_if),
    .register_if  (register_if)
  );
  generate if (1) begin : g_rbr
    rggen_bit_field_if #(32) bit_field_if();
    logic indirect_index;
    `rggen_tie_off_unused_signals(32, 32'h000000ff, bit_field_if)
    assign indirect_index = {register_if[5].value[7+:1]};
    rggen_indirect_register #(
      .READABLE             (1),
      .WRITABLE             (0),
      .ADDRESS_WIDTH        (5),
      .OFFSET_ADDRESS       (5'h00),
      .BUS_WIDTH            (32),
      .DATA_WIDTH           (32),
      .VALUE_WIDTH          (32),
      .INDIRECT_INDEX_WIDTH (1),
      .INDIRECT_INDEX_VALUE ({1'h0})
    ) u_register (
      .i_clk            (i_clk),
      .i_rst_n          (i_rst_n),
      .register_if      (register_if[0]),
      .i_indirect_index (indirect_index),
      .bit_field_if     (bit_field_if)
    );
    if (1) begin : g_rbr
      rggen_bit_field_if #(8) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 0, 8)
      rggen_bit_field #(
        .WIDTH              (8),
        .STORAGE            (0),
        .EXTERNAL_READ_DATA (1),
        .TRIGGER            (1)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (o_rbr_read_trigger),
        .i_sw_write_enable  ('0),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            (i_rbr),
        .i_mask             ('1),
        .o_value            (),
        .o_value_unmasked   ()
      );
    end
  end endgenerate
  generate if (1) begin : g_thr
    rggen_bit_field_if #(32) bit_field_if();
    logic indirect_index;
    `rggen_tie_off_unused_signals(32, 32'h000000ff, bit_field_if)
    assign indirect_index = {register_if[5].value[7+:1]};
    rggen_indirect_register #(
      .READABLE             (0),
      .WRITABLE             (1),
      .ADDRESS_WIDTH        (5),
      .OFFSET_ADDRESS       (5'h00),
      .BUS_WIDTH            (32),
      .DATA_WIDTH           (32),
      .VALUE_WIDTH          (32),
      .INDIRECT_INDEX_WIDTH (1),
      .INDIRECT_INDEX_VALUE ({1'h0})
    ) u_register (
      .i_clk            (i_clk),
      .i_rst_n          (i_rst_n),
      .register_if      (register_if[1]),
      .i_indirect_index (indirect_index),
      .bit_field_if     (bit_field_if)
    );
    if (1) begin : g_thr
      localparam bit [7:0] INITIAL_VALUE = 8'hff;
      rggen_bit_field_if #(8) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 0, 8)
      rggen_bit_field #(
        .WIDTH          (8),
        .INITIAL_VALUE  (INITIAL_VALUE),
        .SW_READ_ACTION (RGGEN_READ_NONE),
        .SW_WRITE_ONCE  (0),
        .TRIGGER        (1)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (o_thr_write_trigger),
        .o_read_trigger     (),
        .i_sw_write_enable  ('1),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            ('0),
        .i_mask             ('1),
        .o_value            (o_thr),
        .o_value_unmasked   ()
      );
    end
  end endgenerate
  generate if (1) begin : g_ier
    rggen_bit_field_if #(32) bit_field_if();
    logic indirect_index;
    `rggen_tie_off_unused_signals(32, 32'h0000000f, bit_field_if)
    assign indirect_index = {register_if[5].value[7+:1]};
    rggen_indirect_register #(
      .READABLE             (1),
      .WRITABLE             (1),
      .ADDRESS_WIDTH        (5),
      .OFFSET_ADDRESS       (5'h04),
      .BUS_WIDTH            (32),
      .DATA_WIDTH           (32),
      .VALUE_WIDTH          (32),
      .INDIRECT_INDEX_WIDTH (1),
      .INDIRECT_INDEX_VALUE ({1'h0})
    ) u_register (
      .i_clk            (i_clk),
      .i_rst_n          (i_rst_n),
      .register_if      (register_if[2]),
      .i_indirect_index (indirect_index),
      .bit_field_if     (bit_field_if)
    );
    if (1) begin : g_erbfi
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 0, 1)
      rggen_bit_field #(
        .WIDTH          (1),
        .INITIAL_VALUE  (INITIAL_VALUE),
        .SW_WRITE_ONCE  (0),
        .TRIGGER        (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('1),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            ('0),
        .i_mask             ('1),
        .o_value            (o_ier_erbfi),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_etbei
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 1, 1)
      rggen_bit_field #(
        .WIDTH          (1),
        .INITIAL_VALUE  (INITIAL_VALUE),
        .SW_WRITE_ONCE  (0),
        .TRIGGER        (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('1),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            ('0),
        .i_mask             ('1),
        .o_value            (o_ier_etbei),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_elsi
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 2, 1)
      rggen_bit_field #(
        .WIDTH          (1),
        .INITIAL_VALUE  (INITIAL_VALUE),
        .SW_WRITE_ONCE  (0),
        .TRIGGER        (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('1),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            ('0),
        .i_mask             ('1),
        .o_value            (o_ier_elsi),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_edssi
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 3, 1)
      rggen_bit_field #(
        .WIDTH          (1),
        .INITIAL_VALUE  (INITIAL_VALUE),
        .SW_WRITE_ONCE  (0),
        .TRIGGER        (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('1),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            ('0),
        .i_mask             ('1),
        .o_value            (o_ier_edssi),
        .o_value_unmasked   ()
      );
    end
  end endgenerate
  generate if (1) begin : g_iir
    rggen_bit_field_if #(32) bit_field_if();
    `rggen_tie_off_unused_signals(32, 32'h0000000f, bit_field_if)
    rggen_default_register #(
      .READABLE       (1),
      .WRITABLE       (0),
      .ADDRESS_WIDTH  (5),
      .OFFSET_ADDRESS (5'h08),
      .BUS_WIDTH      (32),
      .DATA_WIDTH     (32),
      .VALUE_WIDTH    (32)
    ) u_register (
      .i_clk        (i_clk),
      .i_rst_n      (i_rst_n),
      .register_if  (register_if[3]),
      .bit_field_if (bit_field_if)
    );
    if (1) begin : g_intpend
      localparam bit INITIAL_VALUE = 1'h1;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 0, 1)
      rggen_bit_field #(
        .WIDTH              (1),
        .STORAGE            (0),
        .EXTERNAL_READ_DATA (1),
        .TRIGGER            (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('0),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            (i_iir_intpend),
        .i_mask             ('1),
        .o_value            (),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_intid2
      localparam bit [2:0] INITIAL_VALUE = 3'h0;
      rggen_bit_field_if #(3) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 1, 3)
      rggen_bit_field #(
        .WIDTH              (3),
        .STORAGE            (0),
        .EXTERNAL_READ_DATA (1),
        .TRIGGER            (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('0),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            (i_iir_intid2),
        .i_mask             ('1),
        .o_value            (),
        .o_value_unmasked   ()
      );
    end
  end endgenerate
  generate if (1) begin : g_fcr
    rggen_bit_field_if #(32) bit_field_if();
    `rggen_tie_off_unused_signals(32, 32'h000000cf, bit_field_if)
    rggen_default_register #(
      .READABLE       (0),
      .WRITABLE       (1),
      .ADDRESS_WIDTH  (5),
      .OFFSET_ADDRESS (5'h08),
      .BUS_WIDTH      (32),
      .DATA_WIDTH     (32),
      .VALUE_WIDTH    (32)
    ) u_register (
      .i_clk        (i_clk),
      .i_rst_n      (i_rst_n),
      .register_if  (register_if[4]),
      .bit_field_if (bit_field_if)
    );
    if (1) begin : g_fifoen
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 0, 1)
      rggen_bit_field #(
        .WIDTH          (1),
        .INITIAL_VALUE  (INITIAL_VALUE),
        .SW_READ_ACTION (RGGEN_READ_NONE),
        .SW_WRITE_ONCE  (0),
        .TRIGGER        (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('1),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            ('0),
        .i_mask             ('1),
        .o_value            (o_fcr_fifoen),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_rcvr_fifo_reset
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 1, 1)
      rggen_bit_field_w01trg #(
        .TRIGGER_VALUE  (1'b1),
        .WIDTH          (1)
      ) u_bit_field (
        .i_clk        (i_clk),
        .i_rst_n      (i_rst_n),
        .bit_field_if (bit_field_sub_if),
        .i_value      ('0),
        .o_trigger    (o_fcr_rcvr_fifo_reset_trigger)
      );
    end
    if (1) begin : g_xmit_fifo_reset
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 2, 1)
      rggen_bit_field_w01trg #(
        .TRIGGER_VALUE  (1'b1),
        .WIDTH          (1)
      ) u_bit_field (
        .i_clk        (i_clk),
        .i_rst_n      (i_rst_n),
        .bit_field_if (bit_field_sub_if),
        .i_value      ('0),
        .o_trigger    (o_fcr_xmit_fifo_reset_trigger)
      );
    end
    if (1) begin : g_dma_mode_select
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 3, 1)
      rggen_bit_field #(
        .WIDTH          (1),
        .INITIAL_VALUE  (INITIAL_VALUE),
        .SW_READ_ACTION (RGGEN_READ_NONE),
        .SW_WRITE_ONCE  (0),
        .TRIGGER        (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('1),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            ('0),
        .i_mask             ('1),
        .o_value            (o_fcr_dma_mode_select),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_rcvr_fifo_trigger_level
      localparam bit [1:0] INITIAL_VALUE = 2'h0;
      rggen_bit_field_if #(2) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 6, 2)
      rggen_bit_field #(
        .WIDTH          (2),
        .INITIAL_VALUE  (INITIAL_VALUE),
        .SW_READ_ACTION (RGGEN_READ_NONE),
        .SW_WRITE_ONCE  (0),
        .TRIGGER        (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('1),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            ('0),
        .i_mask             ('1),
        .o_value            (o_fcr_rcvr_fifo_trigger_level),
        .o_value_unmasked   ()
      );
    end
  end endgenerate
  generate if (1) begin : g_lcr
    rggen_bit_field_if #(32) bit_field_if();
    `rggen_tie_off_unused_signals(32, 32'h000000ff, bit_field_if)
    rggen_default_register #(
      .READABLE       (1),
      .WRITABLE       (1),
      .ADDRESS_WIDTH  (5),
      .OFFSET_ADDRESS (5'h0c),
      .BUS_WIDTH      (32),
      .DATA_WIDTH     (32),
      .VALUE_WIDTH    (32)
    ) u_register (
      .i_clk        (i_clk),
      .i_rst_n      (i_rst_n),
      .register_if  (register_if[5]),
      .bit_field_if (bit_field_if)
    );
    if (1) begin : g_wls
      localparam bit [1:0] INITIAL_VALUE = 2'h3;
      rggen_bit_field_if #(2) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 0, 2)
      rggen_bit_field #(
        .WIDTH          (2),
        .INITIAL_VALUE  (INITIAL_VALUE),
        .SW_WRITE_ONCE  (0),
        .TRIGGER        (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('1),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            ('0),
        .i_mask             ('1),
        .o_value            (o_lcr_wls),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_stb
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 2, 1)
      rggen_bit_field #(
        .WIDTH          (1),
        .INITIAL_VALUE  (INITIAL_VALUE),
        .SW_WRITE_ONCE  (0),
        .TRIGGER        (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('1),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            ('0),
        .i_mask             ('1),
        .o_value            (o_lcr_stb),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_pen
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 3, 1)
      rggen_bit_field #(
        .WIDTH          (1),
        .INITIAL_VALUE  (INITIAL_VALUE),
        .SW_WRITE_ONCE  (0),
        .TRIGGER        (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('1),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            ('0),
        .i_mask             ('1),
        .o_value            (o_lcr_pen),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_eps
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 4, 1)
      rggen_bit_field #(
        .WIDTH          (1),
        .INITIAL_VALUE  (INITIAL_VALUE),
        .SW_WRITE_ONCE  (0),
        .TRIGGER        (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('1),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            ('0),
        .i_mask             ('1),
        .o_value            (o_lcr_eps),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_stick_parity
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 5, 1)
      rggen_bit_field #(
        .WIDTH          (1),
        .INITIAL_VALUE  (INITIAL_VALUE),
        .SW_WRITE_ONCE  (0),
        .TRIGGER        (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('1),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            ('0),
        .i_mask             ('1),
        .o_value            (o_lcr_stick_parity),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_set_break
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 6, 1)
      rggen_bit_field #(
        .WIDTH          (1),
        .INITIAL_VALUE  (INITIAL_VALUE),
        .SW_WRITE_ONCE  (0),
        .TRIGGER        (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('1),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            ('0),
        .i_mask             ('1),
        .o_value            (o_lcr_set_break),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_dlab
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 7, 1)
      rggen_bit_field #(
        .WIDTH          (1),
        .INITIAL_VALUE  (INITIAL_VALUE),
        .SW_WRITE_ONCE  (0),
        .TRIGGER        (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('1),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            ('0),
        .i_mask             ('1),
        .o_value            (o_lcr_dlab),
        .o_value_unmasked   ()
      );
    end
  end endgenerate
  generate if (1) begin : g_mrc
    rggen_bit_field_if #(32) bit_field_if();
    `rggen_tie_off_unused_signals(32, 32'h0000001f, bit_field_if)
    rggen_default_register #(
      .READABLE       (1),
      .WRITABLE       (1),
      .ADDRESS_WIDTH  (5),
      .OFFSET_ADDRESS (5'h10),
      .BUS_WIDTH      (32),
      .DATA_WIDTH     (32),
      .VALUE_WIDTH    (32)
    ) u_register (
      .i_clk        (i_clk),
      .i_rst_n      (i_rst_n),
      .register_if  (register_if[6]),
      .bit_field_if (bit_field_if)
    );
    if (1) begin : g_dtr
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 0, 1)
      rggen_bit_field #(
        .WIDTH          (1),
        .INITIAL_VALUE  (INITIAL_VALUE),
        .SW_WRITE_ONCE  (0),
        .TRIGGER        (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('1),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            ('0),
        .i_mask             ('1),
        .o_value            (o_mrc_dtr),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_rts
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 1, 1)
      rggen_bit_field #(
        .WIDTH          (1),
        .INITIAL_VALUE  (INITIAL_VALUE),
        .SW_WRITE_ONCE  (0),
        .TRIGGER        (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('1),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            ('0),
        .i_mask             ('1),
        .o_value            (o_mrc_rts),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_out1
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 2, 1)
      rggen_bit_field #(
        .WIDTH          (1),
        .INITIAL_VALUE  (INITIAL_VALUE),
        .SW_WRITE_ONCE  (0),
        .TRIGGER        (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('1),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            ('0),
        .i_mask             ('1),
        .o_value            (o_mrc_out1),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_out2
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 3, 1)
      rggen_bit_field #(
        .WIDTH          (1),
        .INITIAL_VALUE  (INITIAL_VALUE),
        .SW_WRITE_ONCE  (0),
        .TRIGGER        (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('1),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            ('0),
        .i_mask             ('1),
        .o_value            (o_mrc_out2),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_loop
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 4, 1)
      rggen_bit_field #(
        .WIDTH          (1),
        .INITIAL_VALUE  (INITIAL_VALUE),
        .SW_WRITE_ONCE  (0),
        .TRIGGER        (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('1),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            ('0),
        .i_mask             ('1),
        .o_value            (o_mrc_loop),
        .o_value_unmasked   ()
      );
    end
  end endgenerate
  generate if (1) begin : g_lsr
    rggen_bit_field_if #(32) bit_field_if();
    `rggen_tie_off_unused_signals(32, 32'h000000ff, bit_field_if)
    rggen_default_register #(
      .READABLE       (1),
      .WRITABLE       (0),
      .ADDRESS_WIDTH  (5),
      .OFFSET_ADDRESS (5'h14),
      .BUS_WIDTH      (32),
      .DATA_WIDTH     (32),
      .VALUE_WIDTH    (32)
    ) u_register (
      .i_clk        (i_clk),
      .i_rst_n      (i_rst_n),
      .register_if  (register_if[7]),
      .bit_field_if (bit_field_if)
    );
    if (1) begin : g_dr
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 0, 1)
      rggen_bit_field #(
        .WIDTH              (1),
        .STORAGE            (0),
        .EXTERNAL_READ_DATA (1),
        .TRIGGER            (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('0),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            (i_lsr_dr),
        .i_mask             ('1),
        .o_value            (),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_oe
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 1, 1)
      rggen_bit_field #(
        .WIDTH              (1),
        .STORAGE            (0),
        .EXTERNAL_READ_DATA (1),
        .TRIGGER            (1)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (o_lsr_oe_read_trigger),
        .i_sw_write_enable  ('0),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            (i_lsr_oe),
        .i_mask             ('1),
        .o_value            (),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_pe
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 2, 1)
      rggen_bit_field #(
        .WIDTH              (1),
        .STORAGE            (0),
        .EXTERNAL_READ_DATA (1),
        .TRIGGER            (1)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (o_lsr_pe_read_trigger),
        .i_sw_write_enable  ('0),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            (i_lsr_pe),
        .i_mask             ('1),
        .o_value            (),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_fe
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 3, 1)
      rggen_bit_field #(
        .WIDTH              (1),
        .STORAGE            (0),
        .EXTERNAL_READ_DATA (1),
        .TRIGGER            (1)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (o_lsr_fe_read_trigger),
        .i_sw_write_enable  ('0),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            (i_lsr_fe),
        .i_mask             ('1),
        .o_value            (),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_bi
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 4, 1)
      rggen_bit_field #(
        .WIDTH              (1),
        .STORAGE            (0),
        .EXTERNAL_READ_DATA (1),
        .TRIGGER            (1)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (o_lsr_bi_read_trigger),
        .i_sw_write_enable  ('0),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            (i_lsr_bi),
        .i_mask             ('1),
        .o_value            (),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_thre
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 5, 1)
      rggen_bit_field #(
        .WIDTH              (1),
        .STORAGE            (0),
        .EXTERNAL_READ_DATA (1),
        .TRIGGER            (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('0),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            (i_lsr_thre),
        .i_mask             ('1),
        .o_value            (),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_temt
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 6, 1)
      rggen_bit_field #(
        .WIDTH              (1),
        .STORAGE            (0),
        .EXTERNAL_READ_DATA (1),
        .TRIGGER            (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('0),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            (i_lsr_temt),
        .i_mask             ('1),
        .o_value            (),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_error_in_rcvr_fifo
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 7, 1)
      rggen_bit_field #(
        .WIDTH              (1),
        .STORAGE            (0),
        .EXTERNAL_READ_DATA (1),
        .TRIGGER            (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('0),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            (i_lsr_error_in_rcvr_fifo),
        .i_mask             ('1),
        .o_value            (),
        .o_value_unmasked   ()
      );
    end
  end endgenerate
  generate if (1) begin : g_msr
    rggen_bit_field_if #(32) bit_field_if();
    `rggen_tie_off_unused_signals(32, 32'h000000ff, bit_field_if)
    rggen_default_register #(
      .READABLE       (1),
      .WRITABLE       (0),
      .ADDRESS_WIDTH  (5),
      .OFFSET_ADDRESS (5'h18),
      .BUS_WIDTH      (32),
      .DATA_WIDTH     (32),
      .VALUE_WIDTH    (32)
    ) u_register (
      .i_clk        (i_clk),
      .i_rst_n      (i_rst_n),
      .register_if  (register_if[8]),
      .bit_field_if (bit_field_if)
    );
    if (1) begin : g_dcts
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 0, 1)
      rggen_bit_field #(
        .WIDTH              (1),
        .STORAGE            (0),
        .EXTERNAL_READ_DATA (1),
        .TRIGGER            (1)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (o_msr_dcts_read_trigger),
        .i_sw_write_enable  ('0),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            (i_msr_dcts),
        .i_mask             ('1),
        .o_value            (),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_ddsr
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 1, 1)
      rggen_bit_field #(
        .WIDTH              (1),
        .STORAGE            (0),
        .EXTERNAL_READ_DATA (1),
        .TRIGGER            (1)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (o_msr_ddsr_read_trigger),
        .i_sw_write_enable  ('0),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            (i_msr_ddsr),
        .i_mask             ('1),
        .o_value            (),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_teri
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 2, 1)
      rggen_bit_field #(
        .WIDTH              (1),
        .STORAGE            (0),
        .EXTERNAL_READ_DATA (1),
        .TRIGGER            (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('0),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            (i_msr_teri),
        .i_mask             ('1),
        .o_value            (),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_ddcd
      localparam bit INITIAL_VALUE = 1'h0;
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 3, 1)
      rggen_bit_field #(
        .WIDTH              (1),
        .STORAGE            (0),
        .EXTERNAL_READ_DATA (1),
        .TRIGGER            (1)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (o_msr_ddcd_read_trigger),
        .i_sw_write_enable  ('0),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            (i_msr_ddcd),
        .i_mask             ('1),
        .o_value            (),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_cts
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 4, 1)
      rggen_bit_field #(
        .WIDTH              (1),
        .STORAGE            (0),
        .EXTERNAL_READ_DATA (1),
        .TRIGGER            (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('0),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            (i_msr_cts),
        .i_mask             ('1),
        .o_value            (),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_dsr
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 5, 1)
      rggen_bit_field #(
        .WIDTH              (1),
        .STORAGE            (0),
        .EXTERNAL_READ_DATA (1),
        .TRIGGER            (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('0),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            (i_msr_dsr),
        .i_mask             ('1),
        .o_value            (),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_ri
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 6, 1)
      rggen_bit_field #(
        .WIDTH              (1),
        .STORAGE            (0),
        .EXTERNAL_READ_DATA (1),
        .TRIGGER            (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('0),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            (i_msr_ri),
        .i_mask             ('1),
        .o_value            (),
        .o_value_unmasked   ()
      );
    end
    if (1) begin : g_dcd
      rggen_bit_field_if #(1) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 7, 1)
      rggen_bit_field #(
        .WIDTH              (1),
        .STORAGE            (0),
        .EXTERNAL_READ_DATA (1),
        .TRIGGER            (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('0),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            (i_msr_dcd),
        .i_mask             ('1),
        .o_value            (),
        .o_value_unmasked   ()
      );
    end
  end endgenerate
  generate if (1) begin : g_scratch
    rggen_bit_field_if #(32) bit_field_if();
    `rggen_tie_off_unused_signals(32, 32'h000000ff, bit_field_if)
    rggen_default_register #(
      .READABLE       (1),
      .WRITABLE       (1),
      .ADDRESS_WIDTH  (5),
      .OFFSET_ADDRESS (5'h1c),
      .BUS_WIDTH      (32),
      .DATA_WIDTH     (32),
      .VALUE_WIDTH    (32)
    ) u_register (
      .i_clk        (i_clk),
      .i_rst_n      (i_rst_n),
      .register_if  (register_if[9]),
      .bit_field_if (bit_field_if)
    );
    if (1) begin : g_scratch
      localparam bit [7:0] INITIAL_VALUE = 8'h00;
      rggen_bit_field_if #(8) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 0, 8)
      rggen_bit_field #(
        .WIDTH          (8),
        .INITIAL_VALUE  (INITIAL_VALUE),
        .SW_WRITE_ONCE  (0),
        .TRIGGER        (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('1),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            ('0),
        .i_mask             ('1),
        .o_value            (o_scratch),
        .o_value_unmasked   ()
      );
    end
  end endgenerate
  generate if (1) begin : g_dll
    rggen_bit_field_if #(32) bit_field_if();
    logic indirect_index;
    `rggen_tie_off_unused_signals(32, 32'h000000ff, bit_field_if)
    assign indirect_index = {register_if[5].value[7+:1]};
    rggen_indirect_register #(
      .READABLE             (1),
      .WRITABLE             (1),
      .ADDRESS_WIDTH        (5),
      .OFFSET_ADDRESS       (5'h00),
      .BUS_WIDTH            (32),
      .DATA_WIDTH           (32),
      .VALUE_WIDTH          (32),
      .INDIRECT_INDEX_WIDTH (1),
      .INDIRECT_INDEX_VALUE ({1'h1})
    ) u_register (
      .i_clk            (i_clk),
      .i_rst_n          (i_rst_n),
      .register_if      (register_if[10]),
      .i_indirect_index (indirect_index),
      .bit_field_if     (bit_field_if)
    );
    if (1) begin : g_dll
      rggen_bit_field_if #(8) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 0, 8)
      rggen_bit_field #(
        .WIDTH          (8),
        .INITIAL_VALUE  (DLL_INITIAL_VALUE),
        .SW_WRITE_ONCE  (0),
        .TRIGGER        (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('1),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            ('0),
        .i_mask             ('1),
        .o_value            (o_dll),
        .o_value_unmasked   ()
      );
    end
  end endgenerate
  generate if (1) begin : g_dlm
    rggen_bit_field_if #(32) bit_field_if();
    logic indirect_index;
    `rggen_tie_off_unused_signals(32, 32'h000000ff, bit_field_if)
    assign indirect_index = {register_if[5].value[7+:1]};
    rggen_indirect_register #(
      .READABLE             (1),
      .WRITABLE             (1),
      .ADDRESS_WIDTH        (5),
      .OFFSET_ADDRESS       (5'h04),
      .BUS_WIDTH            (32),
      .DATA_WIDTH           (32),
      .VALUE_WIDTH          (32),
      .INDIRECT_INDEX_WIDTH (1),
      .INDIRECT_INDEX_VALUE ({1'h1})
    ) u_register (
      .i_clk            (i_clk),
      .i_rst_n          (i_rst_n),
      .register_if      (register_if[11]),
      .i_indirect_index (indirect_index),
      .bit_field_if     (bit_field_if)
    );
    if (1) begin : g_dlm
      rggen_bit_field_if #(8) bit_field_sub_if();
      `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 0, 8)
      rggen_bit_field #(
        .WIDTH          (8),
        .INITIAL_VALUE  (DLM_INITIAL_VALUE),
        .SW_WRITE_ONCE  (0),
        .TRIGGER        (0)
      ) u_bit_field (
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),
        .bit_field_if       (bit_field_sub_if),
        .o_write_trigger    (),
        .o_read_trigger     (),
        .i_sw_write_enable  ('1),
        .i_hw_write_enable  ('0),
        .i_hw_write_data    ('0),
        .i_hw_set           ('0),
        .i_hw_clear         ('0),
        .i_value            ('0),
        .i_mask             ('1),
        .o_value            (o_dlm),
        .o_value_unmasked   ()
      );
    end
  end endgenerate
endmodule
