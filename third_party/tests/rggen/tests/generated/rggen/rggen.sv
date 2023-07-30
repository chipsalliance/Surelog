/*
:name: RgGen
:description: Full RgGen test
:files: /home/alain/alain-marcel/sv-tests/third_party/cores/rggen-sv-rtl/rggen_rtl_pkg.sv /home/alain/alain-marcel/sv-tests/third_party/cores/rggen-sv-rtl/rggen_or_reducer.sv /home/alain/alain-marcel/sv-tests/third_party/cores/rggen-sv-rtl/rggen_mux.sv /home/alain/alain-marcel/sv-tests/third_party/cores/rggen-sv-rtl/rggen_bit_field_if.sv /home/alain/alain-marcel/sv-tests/third_party/cores/rggen-sv-rtl/rggen_bit_field.sv /home/alain/alain-marcel/sv-tests/third_party/cores/rggen-sv-rtl/rggen_bit_field_w01trg.sv /home/alain/alain-marcel/sv-tests/third_party/cores/rggen-sv-rtl/rggen_register_if.sv /home/alain/alain-marcel/sv-tests/third_party/cores/rggen-sv-rtl/rggen_address_decoder.sv /home/alain/alain-marcel/sv-tests/third_party/cores/rggen-sv-rtl/rggen_register_common.sv /home/alain/alain-marcel/sv-tests/third_party/cores/rggen-sv-rtl/rggen_default_register.sv /home/alain/alain-marcel/sv-tests/third_party/cores/rggen-sv-rtl/rggen_external_register.sv /home/alain/alain-marcel/sv-tests/third_party/cores/rggen-sv-rtl/rggen_indirect_register.sv /home/alain/alain-marcel/sv-tests/third_party/cores/rggen-sv-rtl/rggen_bus_if.sv /home/alain/alain-marcel/sv-tests/third_party/cores/rggen-sv-rtl/rggen_adapter_common.sv /home/alain/alain-marcel/sv-tests/third_party/cores/rggen-sv-rtl/rggen_apb_if.sv /home/alain/alain-marcel/sv-tests/third_party/cores/rggen-sv-rtl/rggen_apb_adapter.sv /home/alain/alain-marcel/sv-tests/third_party/cores/rggen-sv-rtl/rggen_apb_bridge.sv /home/alain/alain-marcel/sv-tests/third_party/cores/rggen-sample/block_0.sv /home/alain/alain-marcel/sv-tests/third_party/cores/rggen-sample/block_1.sv /home/alain/alain-marcel/sv-tests/tests/generated/rggen/rggen.sv
:tags: RgGen
:top_module: rggen
:results_group: cores
:timeout: 100
*/

module rggen;
  import  rggen_rtl_pkg::*;

  logic                       clk;
  logic                       rst_n;
  rggen_apb_if #(16, 32)      apb_if[2]();
  logic [3:0]                 register_0_bit_field_0;
  logic [3:0]                 register_0_bit_field_1;
  logic                       register_0_bit_field_2;
  logic [1:0]                 register_0_bit_field_3;
  logic [1:0]                 register_0_bit_field_4;
  logic [1:0]                 register_0_bit_field_5;
  logic [1:0]                 register_0_bit_field_6;
  logic                       register_1;
  logic [3:0]                 register_2_bit_field_0;
  logic                       register_2_bit_field_2_latch;
  logic [1:0][3:0]            register_2_bit_field_2;
  logic [1:0][3:0]            register_2_bit_field_3;
  logic [3:0]                 register_3_bit_field_0;
  logic [3:0]                 register_3_bit_field_1;
  logic [3:0]                 register_3_bit_field_2_trigger;
  logic [3:0]                 register_3_bit_field_3_trigger;
  logic [3:0]                 register_4_bit_field_0_set;
  logic [3:0]                 register_4_bit_field_0;
  logic [3:0]                 register_4_bit_field_1_set;
  logic [3:0]                 register_4_bit_field_1;
  logic [3:0]                 register_4_bit_field_1_unmasked;
  logic [3:0]                 register_4_bit_field_3_clear;
  logic [3:0]                 register_4_bit_field_3;
  logic                       register_5_bit_field_0_clear;
  logic [1:0]                 register_5_bit_field_0;
  logic [1:0]                 register_5_bit_field_1;
  logic                       register_5_bit_field_2_set;
  logic [1:0]                 register_5_bit_field_2[2];
  logic [1:0]                 register_5_bit_field_3[2];
  logic                       register_5_bit_field_4_enable;
  logic [1:0]                 register_5_bit_field_4;
  logic [1:0]                 register_5_bit_field_5;
  logic [1:0]                 register_5_bit_field_6;
  logic                       register_5_bit_field_7_lock;
  logic [1:0]                 register_5_bit_field_7;
  logic [1:0]                 register_5_bit_field_8;
  logic [1:0]                 register_5_bit_field_9;
  logic [3:0]                 register_6_bit_field_0_set;
  logic [3:0]                 register_6_bit_field_0;
  logic [3:0]                 register_6_bit_field_1_set;
  logic [3:0]                 register_6_bit_field_1;
  logic [3:0]                 register_6_bit_field_1_unmasked;
  logic [3:0]                 register_6_bit_field_3_set;
  logic [3:0]                 register_6_bit_field_3;
  logic [3:0]                 register_6_bit_field_4_set;
  logic [3:0]                 register_6_bit_field_4;
  logic [3:0]                 register_6_bit_field_4_unmasked;
  logic [3:0]                 register_6_bit_field_6_clear;
  logic [3:0]                 register_6_bit_field_6;
  logic [3:0]                 register_6_bit_field_7_clear;
  logic [3:0]                 register_6_bit_field_7;
  logic [3:0]                 register_6_bit_field_8;
  logic [3:0]                 register_6_bit_field_9;
  logic [3:0]                 register_7_bit_field_0;
  logic [3:0]                 register_7_bit_field_1;
  logic [3:0]                 register_7_bit_field_2;
  logic [3:0]                 register_7_bit_field_3;
  logic [3:0]                 register_8_bit_field_0_set;
  logic [3:0]                 register_8_bit_field_0;
  logic [3:0]                 register_8_bit_field_1_clear;
  logic [3:0]                 register_8_bit_field_1;
  logic [3:0]                 register_8_bit_field_2_set;
  logic [3:0]                 register_8_bit_field_2;
  logic [3:0]                 register_8_bit_field_3_clear;
  logic [3:0]                 register_8_bit_field_3;
  logic [3:0]                 register_8_bit_field_4;
  logic [3:0]                 register_8_bit_field_5;
  logic [1:0]                 register_9_bit_field_0;
  logic [1:0]                 register_9_bit_field_1;
  logic [1:0]                 register_9_bit_field_2;
  logic [1:0][1:0]            register_9_bit_field_3;
  logic [1:0]                 register_9_bit_field_4;
  logic [1:0]                 register_9_bit_field_5;
  logic [3:0][3:0][1:0]       register_10_bit_field_0;
  logic [3:0][3:0][1:0]       register_10_bit_field_1;
  logic [3:0][3:0][1:0]       register_10_bit_field_2;
  logic [1:0][3:0][3:0][7:0]  register_11_bit_field_0;
  logic [1:0][3:0][3:0][7:0]  register_11_bit_field_1;
  logic                       register_12_bit_field_0;
  logic                       register_12_bit_field_1;
  logic [1:0]                 register_13_bit_field_0;
  logic [1:0]                 register_13_bit_field_1;
  logic [1:0]                 register_13_bit_field_2;
  logic [1:0]                 register_13_bit_field_3;
  logic                       register_13_bit_field_3_write_trigger;
  logic                       register_13_bit_field_3_read_trigger;
  logic [1:0]                 register_13_bit_field_4;
  logic [1:0]                 register_13_bit_field_5;
  logic [1:0]                 register_13_bit_field_6;
  logic [1:0]                 register_13_bit_field_6_hw_clear;
  logic [1:0]                 register_13_bit_field_7;
  logic [1:0]                 register_13_bit_field_7_hw_set;
  logic [1:0]                 register_13_bit_field_8;
  logic                       register_13_bit_field_8_hw_write_enable;
  logic [1:0]                 register_13_bit_field_8_hw_write_data;
  rggen_bus_if #(8, 32)       register_15_bus_if();

  always_comb begin
    register_2_bit_field_0                  = register_0_bit_field_0;
    register_2_bit_field_2_latch            = register_3_bit_field_3_trigger[0];
    register_2_bit_field_2[0]               = register_0_bit_field_0;
    register_2_bit_field_3[0]               = register_0_bit_field_0;
    register_4_bit_field_0_set              = register_3_bit_field_3_trigger;
    register_4_bit_field_1_set              = register_3_bit_field_3_trigger;
    register_4_bit_field_3_clear            = register_3_bit_field_2_trigger;
    register_5_bit_field_0_clear            = register_3_bit_field_2_trigger[0];
    register_5_bit_field_2_set              = register_3_bit_field_3_trigger[0];
    register_5_bit_field_2[0]               = register_0_bit_field_0[1:0];
    register_5_bit_field_3[0]               = register_0_bit_field_0[1:0];
    register_5_bit_field_4_enable           = register_0_bit_field_2;
    register_5_bit_field_7_lock             = register_0_bit_field_2;
    register_6_bit_field_0_set              = register_3_bit_field_3_trigger;
    register_6_bit_field_1_set              = register_3_bit_field_3_trigger;
    register_6_bit_field_3_set              = register_3_bit_field_3_trigger;
    register_6_bit_field_4_set              = register_3_bit_field_3_trigger;
    register_6_bit_field_6_clear            = register_3_bit_field_2_trigger;
    register_6_bit_field_7_clear            = register_3_bit_field_2_trigger;
    register_8_bit_field_0_set              = register_3_bit_field_3_trigger;
    register_8_bit_field_1_clear            = register_3_bit_field_2_trigger;
    register_8_bit_field_2_set              = register_3_bit_field_3_trigger;
    register_8_bit_field_3_clear            = register_3_bit_field_2_trigger;
    register_9_bit_field_1                  = register_0_bit_field_0[1:0];
    register_9_bit_field_3[1]               = register_0_bit_field_0[1:0];
    register_9_bit_field_4                  = register_0_bit_field_0[1:0];
    register_9_bit_field_5                  = register_0_bit_field_0[1:0];
    register_13_bit_field_1                 = register_13_bit_field_0;
    register_13_bit_field_6_hw_clear        = register_13_bit_field_3_read_trigger;
    register_13_bit_field_7_hw_set          = register_13_bit_field_3_read_trigger;
    register_13_bit_field_8_hw_write_enable = register_13_bit_field_3_write_trigger;
    register_13_bit_field_8_hw_write_data   = register_13_bit_field_3;
  end

  block_0 #(
    .ADDRESS_WIDTH                          (16                       ),
    .PRE_DECODE                             (1                        ),
    .INSERT_SLICER                          (1                        ),
    .BASE_ADDRESS                           (16'h1000                 ),
    .DEFAULT_READ_DATA                      (32'hDEAD_BEAF            ),
    .REGISTER_10_BIT_FIELD_1_INITIAL_VALUE  ({2'h3, 2'h2, 2'h1, 2'h0} )
  ) u_block_0 (
    .i_clk                                      (clk                                      ),
    .i_rst_n                                    (rst_n                                    ),
    .apb_if                                     (apb_if[0]                                ),
    .o_register_0_bit_field_0                   (register_0_bit_field_0                   ),
    .o_register_0_bit_field_1                   (register_0_bit_field_1                   ),
    .o_register_0_bit_field_2                   (register_0_bit_field_2                   ),
    .o_register_0_bit_field_3                   (register_0_bit_field_3                   ),
    .o_register_0_bit_field_4                   (register_0_bit_field_4                   ),
    .o_register_0_bit_field_5                   (register_0_bit_field_5                   ),
    .o_register_0_bit_field_6                   (register_0_bit_field_6                   ),
    .i_register_0_bit_field_6                   (register_0_bit_field_6                   ),
    .o_register_1                               (register_1                               ),
    .i_register_2_bit_field_0                   (register_2_bit_field_0                   ),
    .i_register_2_bit_field_2_latch             (register_2_bit_field_2_latch             ),
    .i_register_2_bit_field_2                   (register_2_bit_field_2[0]                ),
    .o_register_2_bit_field_2                   (register_2_bit_field_2[1]                ),
    .i_register_2_bit_field_3                   (register_2_bit_field_3[0]                ),
    .o_register_2_bit_field_3                   (register_2_bit_field_3[1]                ),
    .o_register_3_bit_field_0                   (register_3_bit_field_0                   ),
    .o_register_3_bit_field_1                   (register_3_bit_field_1                   ),
    .o_register_3_bit_field_2_trigger           (register_3_bit_field_2_trigger           ),
    .o_register_3_bit_field_3_trigger           (register_3_bit_field_3_trigger           ),
    .i_register_4_bit_field_0_set               (register_4_bit_field_0_set               ),
    .o_register_4_bit_field_0                   (register_4_bit_field_0                   ),
    .i_register_4_bit_field_1_set               (register_4_bit_field_1_set               ),
    .o_register_4_bit_field_1                   (register_4_bit_field_1                   ),
    .o_register_4_bit_field_1_unmasked          (register_4_bit_field_1_unmasked          ),
    .i_register_4_bit_field_3_clear             (register_4_bit_field_3_clear             ),
    .o_register_4_bit_field_3                   (register_4_bit_field_3                   ),
    .i_register_5_bit_field_0_clear             (register_5_bit_field_0_clear             ),
    .o_register_5_bit_field_0                   (register_5_bit_field_0                   ),
    .o_register_5_bit_field_1                   (register_5_bit_field_1                   ),
    .i_register_5_bit_field_2_set               (register_5_bit_field_2_set               ),
    .i_register_5_bit_field_2                   (register_5_bit_field_2[0]                ),
    .o_register_5_bit_field_2                   (register_5_bit_field_2[1]                ),
    .i_register_5_bit_field_3                   (register_5_bit_field_3[0]                ),
    .o_register_5_bit_field_3                   (register_5_bit_field_3[1]                ),
    .i_register_5_bit_field_4_enable            (register_5_bit_field_4_enable            ),
    .o_register_5_bit_field_4                   (register_5_bit_field_4                   ),
    .o_register_5_bit_field_5                   (register_5_bit_field_5                   ),
    .o_register_5_bit_field_6                   (register_5_bit_field_6                   ),
    .i_register_5_bit_field_7_lock              (register_5_bit_field_7_lock              ),
    .o_register_5_bit_field_7                   (register_5_bit_field_7                   ),
    .o_register_5_bit_field_8                   (register_5_bit_field_8                   ),
    .o_register_5_bit_field_9                   (register_5_bit_field_9                   ),
    .i_register_6_bit_field_0_set               (register_6_bit_field_0_set               ),
    .o_register_6_bit_field_0                   (register_6_bit_field_0                   ),
    .i_register_6_bit_field_1_set               (register_6_bit_field_1_set               ),
    .o_register_6_bit_field_1                   (register_6_bit_field_1                   ),
    .o_register_6_bit_field_1_unmasked          (register_6_bit_field_1_unmasked          ),
    .i_register_6_bit_field_3_set               (register_6_bit_field_3_set               ),
    .o_register_6_bit_field_3                   (register_6_bit_field_3                   ),
    .i_register_6_bit_field_4_set               (register_6_bit_field_4_set               ),
    .o_register_6_bit_field_4                   (register_6_bit_field_4                   ),
    .o_register_6_bit_field_4_unmasked          (register_6_bit_field_4_unmasked          ),
    .i_register_6_bit_field_6_clear             (register_6_bit_field_6_clear             ),
    .o_register_6_bit_field_6                   (register_6_bit_field_6                   ),
    .i_register_6_bit_field_7_clear             (register_6_bit_field_7_clear             ),
    .o_register_6_bit_field_7                   (register_6_bit_field_7                   ),
    .o_register_6_bit_field_8                   (register_6_bit_field_8                   ),
    .o_register_6_bit_field_9                   (register_6_bit_field_9                   ),
    .o_register_7_bit_field_0                   (register_7_bit_field_0                   ),
    .o_register_7_bit_field_1                   (register_7_bit_field_1                   ),
    .o_register_7_bit_field_2                   (register_7_bit_field_2                   ),
    .o_register_7_bit_field_3                   (register_7_bit_field_3                   ),
    .i_register_8_bit_field_0_set               (register_8_bit_field_0_set               ),
    .o_register_8_bit_field_0                   (register_8_bit_field_0                   ),
    .i_register_8_bit_field_1_clear             (register_8_bit_field_1_clear             ),
    .o_register_8_bit_field_1                   (register_8_bit_field_1                   ),
    .i_register_8_bit_field_2_set               (register_8_bit_field_2_set               ),
    .o_register_8_bit_field_2                   (register_8_bit_field_2                   ),
    .i_register_8_bit_field_3_clear             (register_8_bit_field_3_clear             ),
    .o_register_8_bit_field_3                   (register_8_bit_field_3                   ),
    .o_register_8_bit_field_4                   (register_8_bit_field_4                   ),
    .o_register_8_bit_field_5                   (register_8_bit_field_5                   ),
    .o_register_9_bit_field_0                   (register_9_bit_field_0                   ),
    .o_register_9_bit_field_0_write_trigger     (),
    .o_register_9_bit_field_0_read_trigger      (),
    .i_register_9_bit_field_1                   (register_9_bit_field_1                   ),
    .o_register_9_bit_field_1_read_trigger      (),
    .o_register_9_bit_field_2                   (register_9_bit_field_2                   ),
    .o_register_9_bit_field_2_write_trigger     (),
    .o_register_9_bit_field_3                   (register_9_bit_field_3[0]                ),
    .i_register_9_bit_field_3                   (register_9_bit_field_3[1]                ),
    .o_register_9_bit_field_3_write_trigger     (),
    .o_register_9_bit_field_3_read_trigger      (),
    .i_register_9_bit_field_4                   (register_9_bit_field_4                   ),
    .o_register_9_bit_field_4_trigger           (),
    .i_register_9_bit_field_5                   (register_9_bit_field_5                   ),
    .o_register_9_bit_field_5_trigger           (),
    .o_register_10_bit_field_0                  (register_10_bit_field_0                  ),
    .o_register_10_bit_field_1                  (register_10_bit_field_1                  ),
    .o_register_10_bit_field_2                  (register_10_bit_field_2                  ),
    .o_register_11_bit_field_0                  (register_11_bit_field_0                  ),
    .o_register_11_bit_field_1                  (register_11_bit_field_1                  ),
    .o_register_12_bit_field_0                  (register_12_bit_field_0                  ),
    .o_register_12_bit_field_1                  (register_12_bit_field_1                  ),
    .o_register_13_bit_field_0                  (register_13_bit_field_0                  ),
    .i_register_13_bit_field_1                  (register_13_bit_field_1                  ),
    .o_register_13_bit_field_2                  (register_13_bit_field_2                  ),
    .o_register_13_bit_field_3                  (register_13_bit_field_3                  ),
    .o_register_13_bit_field_3_write_trigger    (register_13_bit_field_3_write_trigger    ),
    .o_register_13_bit_field_3_read_trigger     (register_13_bit_field_3_read_trigger     ),
    .o_register_13_bit_field_4                  (register_13_bit_field_4                  ),
    .o_register_13_bit_field_5                  (register_13_bit_field_5                  ),
    .o_register_13_bit_field_6                  (register_13_bit_field_6                  ),
    .i_register_13_bit_field_6_hw_clear         (register_13_bit_field_6_hw_clear         ),
    .o_register_13_bit_field_7                  (register_13_bit_field_7                  ),
    .i_register_13_bit_field_7_hw_set           (register_13_bit_field_7_hw_set           ),
    .o_register_13_bit_field_8                  (register_13_bit_field_8                  ),
    .i_register_13_bit_field_8_hw_write_enable  (register_13_bit_field_8_hw_write_enable  ),
    .i_register_13_bit_field_8_hw_write_data    (register_13_bit_field_8_hw_write_data    ),
    .register_15_bus_if                         (register_15_bus_if                       )
  );

  rggen_apb_bridge u_bridge (
    .i_clk    (clk                ),
    .i_rst_n  (rst_n              ),
    .bus_if   (register_15_bus_if ),
    .apb_if   (apb_if[1]          )
  );

  block_1 u_block_1 (
    .i_clk                                                    (clk                  ),
    .i_rst_n                                                  (rst_n                ),
    .apb_if                                                   (apb_if[1]            ),
    .o_register_file_0_register_0_bit_field_0                 (),
    .o_register_file_0_register_1_bit_field_0                 (),
    .o_register_file_1_register_0_bit_field_0                 (),
    .o_register_file_1_register_1_bit_field_0                 (),
    .o_register_file_2_register_file_0_register_0_bit_field_0 (),
    .o_register_file_2_register_file_0_register_0_bit_field_1 (),
    .o_register_file_2_register_file_0_register_0_bit_field_2 (),
    .o_register_file_2_register_file_0_register_1_bit_field_0 ()
  );
endmodule
