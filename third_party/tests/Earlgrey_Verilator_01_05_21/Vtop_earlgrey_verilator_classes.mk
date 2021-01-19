# Verilated -*- Makefile -*-
# DESCRIPTION: Verilator output: Make include file with class lists
#
# This file lists generated Verilated files, for including in higher level makefiles.
# See Vtop_earlgrey_verilator.mk for the caller.

### Switches...
# C11 constructs required?  0/1 (always on now)
VM_C11 = 1
# Coverage output mode?  0/1 (from --coverage)
VM_COVERAGE = 0
# Parallel builds?  0/1 (from --output-split)
VM_PARALLEL_BUILDS = 1
# Threaded output mode?  0/1/N threads (from --threads)
VM_THREADS = 4
# Tracing output mode?  0/1 (from --trace/--trace-fst)
VM_TRACE = 1
# Tracing output mode in FST format?  0/1 (from --trace-fst)
VM_TRACE_FST = 1
# Tracing threaded output mode?  0/1/N threads (from --trace-thread)
VM_TRACE_THREADS = 0
# Separate FST writer thread? 0/1 (from --trace-fst with --trace-thread > 0)
VM_TRACE_FST_WRITER_THREAD = 0

### Object file lists...
# Generated module classes, fast-path, compile with highest optimization
VM_CLASSES_FAST += \
	Vtop_earlgrey_verilator \
	Vtop_earlgrey_verilator__1 \
	Vtop_earlgrey_verilator__2 \
	Vtop_earlgrey_verilator__3 \
	Vtop_earlgrey_verilator__4 \
	Vtop_earlgrey_verilator__5 \
	Vtop_earlgrey_verilator__6 \
	Vtop_earlgrey_verilator__7 \
	Vtop_earlgrey_verilator__8 \
	Vtop_earlgrey_verilator__9 \
	Vtop_earlgrey_verilator__10 \
	Vtop_earlgrey_verilator__11 \
	Vtop_earlgrey_verilator__12 \
	Vtop_earlgrey_verilator__13 \
	Vtop_earlgrey_verilator__14 \
	Vtop_earlgrey_verilator__15 \
	Vtop_earlgrey_verilator__16 \
	Vtop_earlgrey_verilator__17 \
	Vtop_earlgrey_verilator__18 \
	Vtop_earlgrey_verilator__19 \
	Vtop_earlgrey_verilator__20 \
	Vtop_earlgrey_verilator__21 \
	Vtop_earlgrey_verilator__22 \
	Vtop_earlgrey_verilator__23 \
	Vtop_earlgrey_verilator__24 \
	Vtop_earlgrey_verilator__25 \
	Vtop_earlgrey_verilator__26 \
	Vtop_earlgrey_verilator__27 \
	Vtop_earlgrey_verilator__28 \
	Vtop_earlgrey_verilator__29 \
	Vtop_earlgrey_verilator__30 \
	Vtop_earlgrey_verilator__31 \
	Vtop_earlgrey_verilator__32 \
	Vtop_earlgrey_verilator__33 \
	Vtop_earlgrey_verilator__34 \
	Vtop_earlgrey_verilator__35 \
	Vtop_earlgrey_verilator__36 \
	Vtop_earlgrey_verilator__37 \
	Vtop_earlgrey_verilator__38 \
	Vtop_earlgrey_verilator__39 \
	Vtop_earlgrey_verilator__40 \
	Vtop_earlgrey_verilator__41 \
	Vtop_earlgrey_verilator__42 \
	Vtop_earlgrey_verilator__43 \
	Vtop_earlgrey_verilator__44 \
	Vtop_earlgrey_verilator__45 \
	Vtop_earlgrey_verilator__46 \
	Vtop_earlgrey_verilator__47 \
	Vtop_earlgrey_verilator__48 \
	Vtop_earlgrey_verilator__49 \
	Vtop_earlgrey_verilator__50 \
	Vtop_earlgrey_verilator__51 \
	Vtop_earlgrey_verilator__52 \
	Vtop_earlgrey_verilator__53 \
	Vtop_earlgrey_verilator__54 \
	Vtop_earlgrey_verilator__55 \
	Vtop_earlgrey_verilator__56 \
	Vtop_earlgrey_verilator__57 \
	Vtop_earlgrey_verilator__58 \
	Vtop_earlgrey_verilator__59 \
	Vtop_earlgrey_verilator__60 \
	Vtop_earlgrey_verilator__61 \
	Vtop_earlgrey_verilator__62 \
	Vtop_earlgrey_verilator__63 \
	Vtop_earlgrey_verilator__64 \
	Vtop_earlgrey_verilator__65 \
	Vtop_earlgrey_verilator__66 \
	Vtop_earlgrey_verilator__67 \
	Vtop_earlgrey_verilator__68 \
	Vtop_earlgrey_verilator__69 \
	Vtop_earlgrey_verilator__70 \
	Vtop_earlgrey_verilator_sw_test_status_if \
	Vtop_earlgrey_verilator_sim_sram_if__A20 \
	Vtop_earlgrey_verilator_edn \
	Vtop_earlgrey_verilator_prim_alert_receiver__Az21 \
	Vtop_earlgrey_verilator_prim_alert_sender \
	Vtop_earlgrey_verilator_tlul_socket_m1__pi28 \
	Vtop_earlgrey_verilator_flash_phy_core \
	Vtop_earlgrey_verilator_flash_phy_core__1 \
	Vtop_earlgrey_verilator_lc_ctrl_reg_top \
	Vtop_earlgrey_verilator_lc_ctrl_reg_pkg \
	Vtop_earlgrey_verilator_pwrmgr_reg_pkg \
	Vtop_earlgrey_verilator_rstmgr_reg_pkg \
	Vtop_earlgrey_verilator_padctrl_reg_pkg \
	Vtop_earlgrey_verilator_pinmux_reg_pkg \
	Vtop_earlgrey_verilator_csrng_reg_pkg \
	Vtop_earlgrey_verilator_otp_ctrl_part_pkg \
	Vtop_earlgrey_verilator_edn_reg_pkg \
	Vtop_earlgrey_verilator_sram_ctrl_reg_pkg \
	Vtop_earlgrey_verilator_prim_lc_sync \
	Vtop_earlgrey_verilator_flash_ctrl_reg_pkg \
	Vtop_earlgrey_verilator_aes_reg_pkg \
	Vtop_earlgrey_verilator_entropy_src_reg_pkg \
	Vtop_earlgrey_verilator_gpio_reg_pkg \
	Vtop_earlgrey_verilator_hmac_reg_pkg \
	Vtop_earlgrey_verilator_keymgr_reg_pkg \
	Vtop_earlgrey_verilator_nmi_gen_reg_pkg \
	Vtop_earlgrey_verilator_otbn_reg_pkg \
	Vtop_earlgrey_verilator_pinmux_pkg \
	Vtop_earlgrey_verilator_rv_timer_reg_pkg \
	Vtop_earlgrey_verilator_spi_device_reg_pkg \
	Vtop_earlgrey_verilator_uart_reg_pkg \
	Vtop_earlgrey_verilator_usbdev_reg_pkg \
	Vtop_earlgrey_verilator_sensor_ctrl_reg_pkg \
	Vtop_earlgrey_verilator_clkmgr_reg_pkg \
	Vtop_earlgrey_verilator_kmac_reg_pkg \
	Vtop_earlgrey_verilator_rv_plic_reg_pkg \
	Vtop_earlgrey_verilator_alert_handler_reg_pkg \
	Vtop_earlgrey_verilator_otbn_stack_snooper_if__SB8 \
	Vtop_earlgrey_verilator_flash_ctrl_pkg \
	Vtop_earlgrey_verilator_tlul_fifo_sync__RCz43_RDz43 \
	Vtop_earlgrey_verilator_prim_generic_flash_bank__pi64 \
	Vtop_earlgrey_verilator_hmac_pkg \
	Vtop_earlgrey_verilator_sha3_pkg \
	Vtop_earlgrey_verilator_otbn_rf_snooper_if \
	Vtop_earlgrey_verilator_otbn_rf_snooper_if__W100 \
	Vtop_earlgrey_verilator_otp_ctrl_reg_pkg \
	Vtop_earlgrey_verilator_prim_flop_2sync__W1 \
	Vtop_earlgrey_verilator_aes_sbox__S0 \
	Vtop_earlgrey_verilator_aes_sbox__S3 \
	Vtop_earlgrey_verilator_aes_sbox__S3__1 \
	Vtop_earlgrey_verilator_aes_sbox__S3__2 \
	Vtop_earlgrey_verilator_aes_sbox__S3__3 \
	Vtop_earlgrey_verilator_aes_sbox__S3__4 \
	Vtop_earlgrey_verilator_aes_sbox__S3__5 \
	Vtop_earlgrey_verilator_aes_sbox__S3__6 \
	Vtop_earlgrey_verilator_aes_sbox__S3__7 \
	Vtop_earlgrey_verilator_aes_sbox__S3__8 \
	Vtop_earlgrey_verilator_aes_sbox__S3__9 \
	Vtop_earlgrey_verilator_aes_sbox__S3__10 \
	Vtop_earlgrey_verilator_aes_sbox__S3__11 \
	Vtop_earlgrey_verilator_aes_pkg \
	Vtop_earlgrey_verilator_aes_sbox_canright_pkg \
	Vtop_earlgrey_verilator___024unit \

# Generated module classes, non-fast-path, compile with low/medium optimization
VM_CLASSES_SLOW += \
	Vtop_earlgrey_verilator__Slow \
	Vtop_earlgrey_verilator__1__Slow \
	Vtop_earlgrey_verilator__2__Slow \
	Vtop_earlgrey_verilator__3__Slow \
	Vtop_earlgrey_verilator__4__Slow \
	Vtop_earlgrey_verilator__5__Slow \
	Vtop_earlgrey_verilator__6__Slow \
	Vtop_earlgrey_verilator__7__Slow \
	Vtop_earlgrey_verilator__8__Slow \
	Vtop_earlgrey_verilator__9__Slow \
	Vtop_earlgrey_verilator__10__Slow \
	Vtop_earlgrey_verilator__11__Slow \
	Vtop_earlgrey_verilator__12__Slow \
	Vtop_earlgrey_verilator__13__Slow \
	Vtop_earlgrey_verilator__14__Slow \
	Vtop_earlgrey_verilator__15__Slow \
	Vtop_earlgrey_verilator__16__Slow \
	Vtop_earlgrey_verilator__17__Slow \
	Vtop_earlgrey_verilator__18__Slow \
	Vtop_earlgrey_verilator__19__Slow \
	Vtop_earlgrey_verilator__20__Slow \
	Vtop_earlgrey_verilator__21__Slow \
	Vtop_earlgrey_verilator__22__Slow \
	Vtop_earlgrey_verilator__23__Slow \
	Vtop_earlgrey_verilator__24__Slow \
	Vtop_earlgrey_verilator__25__Slow \
	Vtop_earlgrey_verilator__26__Slow \
	Vtop_earlgrey_verilator__27__Slow \
	Vtop_earlgrey_verilator__28__Slow \
	Vtop_earlgrey_verilator__29__Slow \
	Vtop_earlgrey_verilator__30__Slow \
	Vtop_earlgrey_verilator__31__Slow \
	Vtop_earlgrey_verilator__32__Slow \
	Vtop_earlgrey_verilator__33__Slow \
	Vtop_earlgrey_verilator__34__Slow \
	Vtop_earlgrey_verilator__35__Slow \
	Vtop_earlgrey_verilator__36__Slow \
	Vtop_earlgrey_verilator__37__Slow \
	Vtop_earlgrey_verilator__38__Slow \
	Vtop_earlgrey_verilator__39__Slow \
	Vtop_earlgrey_verilator__40__Slow \
	Vtop_earlgrey_verilator__41__Slow \
	Vtop_earlgrey_verilator__42__Slow \
	Vtop_earlgrey_verilator__43__Slow \
	Vtop_earlgrey_verilator__44__Slow \
	Vtop_earlgrey_verilator__45__Slow \
	Vtop_earlgrey_verilator__46__Slow \
	Vtop_earlgrey_verilator__47__Slow \
	Vtop_earlgrey_verilator__48__Slow \
	Vtop_earlgrey_verilator__49__Slow \
	Vtop_earlgrey_verilator__50__Slow \
	Vtop_earlgrey_verilator__51__Slow \
	Vtop_earlgrey_verilator__52__Slow \
	Vtop_earlgrey_verilator__53__Slow \
	Vtop_earlgrey_verilator__54__Slow \
	Vtop_earlgrey_verilator__55__Slow \
	Vtop_earlgrey_verilator__56__Slow \
	Vtop_earlgrey_verilator_sw_test_status_if__Slow \
	Vtop_earlgrey_verilator_sim_sram_if__A20__Slow \
	Vtop_earlgrey_verilator_edn__Slow \
	Vtop_earlgrey_verilator_prim_alert_receiver__Az21__Slow \
	Vtop_earlgrey_verilator_prim_alert_sender__Slow \
	Vtop_earlgrey_verilator_tlul_socket_m1__pi28__Slow \
	Vtop_earlgrey_verilator_flash_phy_core__Slow \
	Vtop_earlgrey_verilator_flash_phy_core__1__Slow \
	Vtop_earlgrey_verilator_flash_phy_core__2__Slow \
	Vtop_earlgrey_verilator_lc_ctrl_reg_top__Slow \
	Vtop_earlgrey_verilator_lc_ctrl_reg_pkg__Slow \
	Vtop_earlgrey_verilator_pwrmgr_reg_pkg__Slow \
	Vtop_earlgrey_verilator_rstmgr_reg_pkg__Slow \
	Vtop_earlgrey_verilator_padctrl_reg_pkg__Slow \
	Vtop_earlgrey_verilator_pinmux_reg_pkg__Slow \
	Vtop_earlgrey_verilator_csrng_reg_pkg__Slow \
	Vtop_earlgrey_verilator_otp_ctrl_part_pkg__Slow \
	Vtop_earlgrey_verilator_edn_reg_pkg__Slow \
	Vtop_earlgrey_verilator_sram_ctrl_reg_pkg__Slow \
	Vtop_earlgrey_verilator_prim_lc_sync__Slow \
	Vtop_earlgrey_verilator_flash_ctrl_reg_pkg__Slow \
	Vtop_earlgrey_verilator_aes_reg_pkg__Slow \
	Vtop_earlgrey_verilator_entropy_src_reg_pkg__Slow \
	Vtop_earlgrey_verilator_gpio_reg_pkg__Slow \
	Vtop_earlgrey_verilator_hmac_reg_pkg__Slow \
	Vtop_earlgrey_verilator_keymgr_reg_pkg__Slow \
	Vtop_earlgrey_verilator_nmi_gen_reg_pkg__Slow \
	Vtop_earlgrey_verilator_otbn_reg_pkg__Slow \
	Vtop_earlgrey_verilator_pinmux_pkg__Slow \
	Vtop_earlgrey_verilator_rv_timer_reg_pkg__Slow \
	Vtop_earlgrey_verilator_spi_device_reg_pkg__Slow \
	Vtop_earlgrey_verilator_uart_reg_pkg__Slow \
	Vtop_earlgrey_verilator_usbdev_reg_pkg__Slow \
	Vtop_earlgrey_verilator_sensor_ctrl_reg_pkg__Slow \
	Vtop_earlgrey_verilator_clkmgr_reg_pkg__Slow \
	Vtop_earlgrey_verilator_kmac_reg_pkg__Slow \
	Vtop_earlgrey_verilator_rv_plic_reg_pkg__Slow \
	Vtop_earlgrey_verilator_alert_handler_reg_pkg__Slow \
	Vtop_earlgrey_verilator_otbn_stack_snooper_if__SB8__Slow \
	Vtop_earlgrey_verilator_flash_ctrl_pkg__Slow \
	Vtop_earlgrey_verilator_tlul_fifo_sync__RCz43_RDz43__Slow \
	Vtop_earlgrey_verilator_tlul_fifo_sync__RCz43_RDz43__1__Slow \
	Vtop_earlgrey_verilator_tlul_fifo_sync__RCz43_RDz43__2__Slow \
	Vtop_earlgrey_verilator_prim_generic_flash_bank__pi64__Slow \
	Vtop_earlgrey_verilator_hmac_pkg__Slow \
	Vtop_earlgrey_verilator_sha3_pkg__Slow \
	Vtop_earlgrey_verilator_otbn_rf_snooper_if__Slow \
	Vtop_earlgrey_verilator_otbn_rf_snooper_if__W100__Slow \
	Vtop_earlgrey_verilator_otp_ctrl_reg_pkg__Slow \
	Vtop_earlgrey_verilator_prim_flop_2sync__W1__Slow \
	Vtop_earlgrey_verilator_aes_sbox__S0__Slow \
	Vtop_earlgrey_verilator_aes_sbox__S3__Slow \
	Vtop_earlgrey_verilator_aes_sbox__S3__1__Slow \
	Vtop_earlgrey_verilator_aes_sbox__S3__2__Slow \
	Vtop_earlgrey_verilator_aes_sbox__S3__3__Slow \
	Vtop_earlgrey_verilator_aes_sbox__S3__4__Slow \
	Vtop_earlgrey_verilator_aes_sbox__S3__5__Slow \
	Vtop_earlgrey_verilator_aes_sbox__S3__6__Slow \
	Vtop_earlgrey_verilator_aes_sbox__S3__7__Slow \
	Vtop_earlgrey_verilator_aes_sbox__S3__8__Slow \
	Vtop_earlgrey_verilator_aes_sbox__S3__9__Slow \
	Vtop_earlgrey_verilator_aes_sbox__S3__10__Slow \
	Vtop_earlgrey_verilator_aes_sbox__S3__11__Slow \
	Vtop_earlgrey_verilator_aes_sbox__S3__12__Slow \
	Vtop_earlgrey_verilator_aes_sbox__S3__13__Slow \
	Vtop_earlgrey_verilator_aes_sbox__S3__14__Slow \
	Vtop_earlgrey_verilator_aes_sbox__S3__15__Slow \
	Vtop_earlgrey_verilator_aes_sbox__S3__16__Slow \
	Vtop_earlgrey_verilator_aes_sbox__S3__17__Slow \
	Vtop_earlgrey_verilator_aes_pkg__Slow \
	Vtop_earlgrey_verilator_aes_sbox_canright_pkg__Slow \
	Vtop_earlgrey_verilator___024unit__Slow \

# Generated support classes, fast-path, compile with highest optimization
VM_SUPPORT_FAST += \
	Vtop_earlgrey_verilator__Dpi \
	Vtop_earlgrey_verilator__Trace \
	Vtop_earlgrey_verilator__Trace__1 \
	Vtop_earlgrey_verilator__Trace__2 \
	Vtop_earlgrey_verilator__Trace__3 \
	Vtop_earlgrey_verilator__Trace__4 \
	Vtop_earlgrey_verilator__Trace__5 \
	Vtop_earlgrey_verilator__Trace__6 \
	Vtop_earlgrey_verilator__Trace__7 \
	Vtop_earlgrey_verilator__Trace__8 \
	Vtop_earlgrey_verilator__Trace__9 \
	Vtop_earlgrey_verilator__Trace__10 \
	Vtop_earlgrey_verilator__Trace__11 \
	Vtop_earlgrey_verilator__Trace__12 \
	Vtop_earlgrey_verilator__Trace__13 \
	Vtop_earlgrey_verilator__Trace__14 \
	Vtop_earlgrey_verilator__Trace__15 \
	Vtop_earlgrey_verilator__Trace__16 \

# Generated support classes, non-fast-path, compile with low/medium optimization
VM_SUPPORT_SLOW += \
	Vtop_earlgrey_verilator__Syms \
	Vtop_earlgrey_verilator__Trace__Slow \
	Vtop_earlgrey_verilator__Trace__1__Slow \
	Vtop_earlgrey_verilator__Trace__2__Slow \
	Vtop_earlgrey_verilator__Trace__3__Slow \
	Vtop_earlgrey_verilator__Trace__4__Slow \
	Vtop_earlgrey_verilator__Trace__5__Slow \
	Vtop_earlgrey_verilator__Trace__6__Slow \
	Vtop_earlgrey_verilator__Trace__7__Slow \
	Vtop_earlgrey_verilator__Trace__8__Slow \
	Vtop_earlgrey_verilator__Trace__9__Slow \
	Vtop_earlgrey_verilator__Trace__10__Slow \
	Vtop_earlgrey_verilator__Trace__11__Slow \
	Vtop_earlgrey_verilator__Trace__12__Slow \
	Vtop_earlgrey_verilator__Trace__13__Slow \
	Vtop_earlgrey_verilator__Trace__14__Slow \
	Vtop_earlgrey_verilator__Trace__15__Slow \
	Vtop_earlgrey_verilator__Trace__16__Slow \
	Vtop_earlgrey_verilator__Trace__17__Slow \
	Vtop_earlgrey_verilator__Trace__18__Slow \
	Vtop_earlgrey_verilator__Trace__19__Slow \
	Vtop_earlgrey_verilator__Trace__20__Slow \
	Vtop_earlgrey_verilator__Trace__21__Slow \

# Global classes, need linked once per executable, fast-path, compile with highest optimization
VM_GLOBAL_FAST += \
	verilated \
	verilated_dpi \
	verilated_fst_c \
	verilated_threads \

# Global classes, need linked once per executable, non-fast-path, compile with low/medium optimization
VM_GLOBAL_SLOW += \


# Verilated -*- Makefile -*-
