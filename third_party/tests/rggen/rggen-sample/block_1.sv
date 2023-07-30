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
module block_1
  import rggen_rtl_pkg::*;
#(
  parameter int ADDRESS_WIDTH = 7,
  parameter bit PRE_DECODE = 0,
  parameter bit [ADDRESS_WIDTH-1:0] BASE_ADDRESS = '0,
  parameter bit ERROR_STATUS = 0,
  parameter bit [31:0] DEFAULT_READ_DATA = '0,
  parameter bit INSERT_SLICER = 0
)(
  input logic i_clk,
  input logic i_rst_n,
  rggen_apb_if.slave apb_if,
  output logic [7:0] o_register_file_0_register_0_bit_field_0,
  output logic [7:0] o_register_file_0_register_1_bit_field_0,
  output logic [1:0][7:0] o_register_file_1_register_0_bit_field_0,
  output logic [1:0][7:0] o_register_file_1_register_1_bit_field_0,
  output logic [1:0][1:0][2:0][1:0][3:0] o_register_file_2_register_file_0_register_0_bit_field_0,
  output logic [1:0][1:0][2:0][1:0][3:0] o_register_file_2_register_file_0_register_0_bit_field_1,
  output logic [1:0][1:0][2:0][1:0][3:0] o_register_file_2_register_file_0_register_0_bit_field_2,
  output logic [1:0][1:0] o_register_file_2_register_file_0_register_1_bit_field_0
);
  rggen_register_if #(7, 32, 32) register_if[20]();
  rggen_apb_adapter #(
    .ADDRESS_WIDTH        (ADDRESS_WIDTH),
    .LOCAL_ADDRESS_WIDTH  (7),
    .BUS_WIDTH            (32),
    .REGISTERS            (20),
    .PRE_DECODE           (PRE_DECODE),
    .BASE_ADDRESS         (BASE_ADDRESS),
    .BYTE_SIZE            (128),
    .ERROR_STATUS         (ERROR_STATUS),
    .DEFAULT_READ_DATA    (DEFAULT_READ_DATA),
    .INSERT_SLICER        (INSERT_SLICER)
  ) u_adapter (
    .i_clk        (i_clk),
    .i_rst_n      (i_rst_n),
    .apb_if       (apb_if),
    .register_if  (register_if)
  );
  generate if (1) begin : g_register_file_0
    if (1) begin : g_register_0
      rggen_bit_field_if #(32) bit_field_if();
      `rggen_tie_off_unused_signals(32, 32'h000000ff, bit_field_if)
      rggen_default_register #(
        .READABLE       (1),
        .WRITABLE       (1),
        .ADDRESS_WIDTH  (7),
        .OFFSET_ADDRESS (7'h00),
        .BUS_WIDTH      (32),
        .DATA_WIDTH     (32),
        .VALUE_WIDTH    (32)
      ) u_register (
        .i_clk        (i_clk),
        .i_rst_n      (i_rst_n),
        .register_if  (register_if[0]),
        .bit_field_if (bit_field_if)
      );
      if (1) begin : g_bit_field_0
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
          .o_value            (o_register_file_0_register_0_bit_field_0),
          .o_value_unmasked   ()
        );
      end
    end
    if (1) begin : g_register_1
      rggen_bit_field_if #(32) bit_field_if();
      `rggen_tie_off_unused_signals(32, 32'h000000ff, bit_field_if)
      rggen_default_register #(
        .READABLE       (1),
        .WRITABLE       (1),
        .ADDRESS_WIDTH  (7),
        .OFFSET_ADDRESS (7'h04),
        .BUS_WIDTH      (32),
        .DATA_WIDTH     (32),
        .VALUE_WIDTH    (32)
      ) u_register (
        .i_clk        (i_clk),
        .i_rst_n      (i_rst_n),
        .register_if  (register_if[1]),
        .bit_field_if (bit_field_if)
      );
      if (1) begin : g_bit_field_0
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
          .o_value            (o_register_file_0_register_1_bit_field_0),
          .o_value_unmasked   ()
        );
      end
    end
  end endgenerate
  generate if (1) begin : g_register_file_1
    if (1) begin : g_register_0
      genvar i;
      for (i = 0;i < 2;++i) begin : g
        rggen_bit_field_if #(32) bit_field_if();
        logic [15:0] indirect_index;
        `rggen_tie_off_unused_signals(32, 32'h000000ff, bit_field_if)
        assign indirect_index = {register_if[0].value[0+:8], register_if[1].value[0+:8]};
        rggen_indirect_register #(
          .READABLE             (1),
          .WRITABLE             (1),
          .ADDRESS_WIDTH        (7),
          .OFFSET_ADDRESS       (7'h10),
          .BUS_WIDTH            (32),
          .DATA_WIDTH           (32),
          .VALUE_WIDTH          (32),
          .INDIRECT_INDEX_WIDTH (16),
          .INDIRECT_INDEX_VALUE ({i[0+:8], 8'h00})
        ) u_register (
          .i_clk            (i_clk),
          .i_rst_n          (i_rst_n),
          .register_if      (register_if[2+i]),
          .i_indirect_index (indirect_index),
          .bit_field_if     (bit_field_if)
        );
        if (1) begin : g_bit_field_0
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
            .o_value            (o_register_file_1_register_0_bit_field_0[i]),
            .o_value_unmasked   ()
          );
        end
      end
    end
    if (1) begin : g_register_1
      genvar i;
      for (i = 0;i < 2;++i) begin : g
        rggen_bit_field_if #(32) bit_field_if();
        logic [15:0] indirect_index;
        `rggen_tie_off_unused_signals(32, 32'h000000ff, bit_field_if)
        assign indirect_index = {register_if[0].value[0+:8], register_if[1].value[0+:8]};
        rggen_indirect_register #(
          .READABLE             (1),
          .WRITABLE             (1),
          .ADDRESS_WIDTH        (7),
          .OFFSET_ADDRESS       (7'h10),
          .BUS_WIDTH            (32),
          .DATA_WIDTH           (32),
          .VALUE_WIDTH          (32),
          .INDIRECT_INDEX_WIDTH (16),
          .INDIRECT_INDEX_VALUE ({i[0+:8], 8'h01})
        ) u_register (
          .i_clk            (i_clk),
          .i_rst_n          (i_rst_n),
          .register_if      (register_if[4+i]),
          .i_indirect_index (indirect_index),
          .bit_field_if     (bit_field_if)
        );
        if (1) begin : g_bit_field_0
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
            .o_value            (o_register_file_1_register_1_bit_field_0[i]),
            .o_value_unmasked   ()
          );
        end
      end
    end
  end endgenerate
  generate if (1) begin : g_register_file_2
    genvar i;
    for (i = 0;i < 2;++i) begin : g
      if (1) begin : g_register_file_0
        if (1) begin : g_register_0
          genvar j;
          genvar k;
          for (j = 0;j < 2;++j) begin : g
            for (k = 0;k < 3;++k) begin : g
              rggen_bit_field_if #(32) bit_field_if();
              `rggen_tie_off_unused_signals(32, 32'h00ffffff, bit_field_if)
              rggen_default_register #(
                .READABLE       (1),
                .WRITABLE       (1),
                .ADDRESS_WIDTH  (7),
                .OFFSET_ADDRESS (7'h20+7'(32*i)+7'(4*(3*j+k))),
                .BUS_WIDTH      (32),
                .DATA_WIDTH     (32),
                .VALUE_WIDTH    (32)
              ) u_register (
                .i_clk        (i_clk),
                .i_rst_n      (i_rst_n),
                .register_if  (register_if[6+7*i+3*j+k]),
                .bit_field_if (bit_field_if)
              );
              if (1) begin : g_bit_field_0
                genvar l;
                for (l = 0;l < 2;++l) begin : g
                  localparam bit [3:0] INITIAL_VALUE = 4'h0;
                  rggen_bit_field_if #(4) bit_field_sub_if();
                  `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 0+4*l, 4)
                  rggen_bit_field #(
                    .WIDTH          (4),
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
                    .o_value            (o_register_file_2_register_file_0_register_0_bit_field_0[i][j][k][l]),
                    .o_value_unmasked   ()
                  );
                end
              end
              if (1) begin : g_bit_field_1
                genvar l;
                for (l = 0;l < 2;++l) begin : g
                  localparam bit [3:0] INITIAL_VALUE = 4'h0;
                  rggen_bit_field_if #(4) bit_field_sub_if();
                  `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 8+4*l, 4)
                  rggen_bit_field #(
                    .WIDTH                    (4),
                    .INITIAL_VALUE            (INITIAL_VALUE),
                    .SW_WRITE_ENABLE_POLARITY (RGGEN_ACTIVE_HIGH)
                  ) u_bit_field (
                    .i_clk              (i_clk),
                    .i_rst_n            (i_rst_n),
                    .bit_field_if       (bit_field_sub_if),
                    .o_write_trigger    (),
                    .o_read_trigger     (),
                    .i_sw_write_enable  (register_if[0].value[0+:1]),
                    .i_hw_write_enable  ('0),
                    .i_hw_write_data    ('0),
                    .i_hw_set           ('0),
                    .i_hw_clear         ('0),
                    .i_value            ('0),
                    .i_mask             ('1),
                    .o_value            (o_register_file_2_register_file_0_register_0_bit_field_1[i][j][k][l]),
                    .o_value_unmasked   ()
                  );
                end
              end
              if (1) begin : g_bit_field_2
                genvar l;
                for (l = 0;l < 2;++l) begin : g
                  localparam bit [3:0] INITIAL_VALUE = 4'h0;
                  rggen_bit_field_if #(4) bit_field_sub_if();
                  `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 16+4*l, 4)
                  rggen_bit_field #(
                    .WIDTH                    (4),
                    .INITIAL_VALUE            (INITIAL_VALUE),
                    .SW_WRITE_ENABLE_POLARITY (RGGEN_ACTIVE_LOW)
                  ) u_bit_field (
                    .i_clk              (i_clk),
                    .i_rst_n            (i_rst_n),
                    .bit_field_if       (bit_field_sub_if),
                    .o_write_trigger    (),
                    .o_read_trigger     (),
                    .i_sw_write_enable  (register_if[6+7*i+6].value[0+1*l+:1]),
                    .i_hw_write_enable  ('0),
                    .i_hw_write_data    ('0),
                    .i_hw_set           ('0),
                    .i_hw_clear         ('0),
                    .i_value            ('0),
                    .i_mask             ('1),
                    .o_value            (o_register_file_2_register_file_0_register_0_bit_field_2[i][j][k][l]),
                    .o_value_unmasked   ()
                  );
                end
              end
            end
          end
        end
        if (1) begin : g_register_1
          rggen_bit_field_if #(32) bit_field_if();
          `rggen_tie_off_unused_signals(32, 32'h00000003, bit_field_if)
          rggen_default_register #(
            .READABLE       (1),
            .WRITABLE       (1),
            .ADDRESS_WIDTH  (7),
            .OFFSET_ADDRESS (7'h20+7'(32*i)+7'h18),
            .BUS_WIDTH      (32),
            .DATA_WIDTH     (32),
            .VALUE_WIDTH    (32)
          ) u_register (
            .i_clk        (i_clk),
            .i_rst_n      (i_rst_n),
            .register_if  (register_if[6+7*i+6]),
            .bit_field_if (bit_field_if)
          );
          if (1) begin : g_bit_field_0
            genvar j;
            for (j = 0;j < 2;++j) begin : g
              localparam bit INITIAL_VALUE = 1'h0;
              rggen_bit_field_if #(1) bit_field_sub_if();
              `rggen_connect_bit_field_if(bit_field_if, bit_field_sub_if, 0+1*j, 1)
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
                .o_value            (o_register_file_2_register_file_0_register_1_bit_field_0[i][j]),
                .o_value_unmasked   ()
              );
            end
          end
        end
      end
    end
  end endgenerate
endmodule
