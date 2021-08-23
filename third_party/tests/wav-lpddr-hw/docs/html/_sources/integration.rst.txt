Integration
===========

The Wavious DDR PHY supports LPDDR4x and LPDDR5 standards and is provided in a 1x32 configuration (Memory Controller side) consisting of two 1x16 channels (DRAM side). The 1x32 channel configuration is chosen to mitigate MCU+SRAM area overhead to DRAM interface width.

.. note ::
  * 1x16 configuation may be supported in a future release version.
  * LPDDR5 configuration support may be limited in current release version.
  * DDR5 configuation may be supported in a future release version.
  * HBM configuation may be supported in a future release version.

Design Files
------------

.. literalinclude:: rtl_tree.txt

Configurations
--------------

   * Protocol: LP4x, LP5
   * Channels: 1x16, 2x16, 4x16, 1x32, etc.
   * Frequency (MHz): 422.4, 806.4, 1612.8, 2112, 3187.2, etc.
   * Frequency Ratio: 1:2, 1:4
   * Rank: Single, dual
   * Signaling: Terminated/unterminated, differential/single-ended (CK, WCK)

.. note ::
  * Frequencies are not limit ot those listed.
  * LPDDR5 configuration support may be limited in current release version.
  * 1:1 and 1:8 frequency ratio may be supported in future release version.
  * Currently, only the 1x32 channel configuration is available. Other configuraitons may be supported in future release version.

Ports
-----

The Wavious DDR PHY standard interfaces include: 1149.1 TAP, DFIv5.0, AHB-Lite, and LPDDR4x/LPDDR5. For specific signal descriptions and functions, please refer to the interface protocol specifications.

.. table::
    :widths: 30 10 10 50

    ========================== ===========  =======================  ==============================================================================================================
    Port Name                  Direction    Width                    Description
    ========================== ===========  =======================  ==============================================================================================================
    **Global Clocks and Reset**
    ---------------------------------------------------------------  --------------------------------------------------------------------------------------------------------------
    i_phy_rst                  input        1                        Global PHY reset
    i_ana_refclk               input        1                        Analog reference clock @38.4Mhz (low jitter)
    i_refclk                   input        1                        Reference clock @38.4Mhz
    o_refclk_on                output       1                        Refence clock on request
    i_refclk_alt               input        1                        Reference clock alternative
    **Test**
    ---------------------------------------------------------------  --------------------------------------------------------------------------------------------------------------
    i_gpb                      input        [7:0]                    General purpose bus
    o_gpb                      output       [7:0]                    General purpose bus
    o_debug                    output       [31:0]                   Debug bus (low frequency)
    i_freeze_n                 input        1                        Freeze IO (active low)
    i_hiz_n                    input        1                        High impedance (active low)
    i_iddq_mode                input        1                        IDDQ mode enable
    o_dtst                     output       1                        Digital clock test (high frequency)
    **Interrupts**
    ---------------------------------------------------------------  --------------------------------------------------------------------------------------------------------------
    i_irq                      input        [3:0]                    Interrupt
    o_irq                      output       [1:0]                    Interrupt
    **DFT**
    ---------------------------------------------------------------  --------------------------------------------------------------------------------------------------------------
    i_scan_mode                input        1                        Scan mode enable
    i_scan_clk                 input        1                        Scan clock
    i_scan_en                  input        1                        Scan shift enable
    i_scan_freq_en             input        [7:0]                    Scan clock tree frequency enable
    i_scan_cgc_ctrl            input        1                        CGC override enable
    i_scan_rst_ctrl            input        1                        Reset override enable
    i_scan_set_ctrl            input        1                        Set override enable
    i_scan                     input        [15:0]                   Scan chain in
    o_scan                     output       [15:0]                   Scan chain out
    **TAP**
    ---------------------------------------------------------------  --------------------------------------------------------------------------------------------------------------
    i_jtag_tck                 input        1
    i_jtag_trst_n              input        1
    i_jtag_tms                 input        1
    i_jtag_tdi                 input        1
    o_jtag_tdo                 output       1
    **AHB**
    ---------------------------------------------------------------  --------------------------------------------------------------------------------------------------------------
    i_ahb_clk                  input        1
    o_ahb_clk_on               output       1                        AHB clock on request
    i_ahb_rst                  input        1
    i_ahb_csr_rst              input        1                        AHB CSR reset
    **AHB Slave**
    ---------------------------------------------------------------  --------------------------------------------------------------------------------------------------------------
    i_ahb_haddr                input        [31:0]
    i_ahb_hwrite               input        1
    i_ahb_hsel                 input        1
    i_ahb_hwdata               input        [31:0]
    i_ahb_htrans               input        [1:0]
    i_ahb_hsize                input        [2:0]
    i_ahb_hburst               input        [2:0]
    i_ahb_hreadyin             input        1                        HREADY
    o_ahb_hready               output       1                        HREADYOUT
    o_ahb_hrdata               output       [31:0]
    o_ahb_hresp                output       [1:0]
    **AHB Master**
    ---------------------------------------------------------------  --------------------------------------------------------------------------------------------------------------
    o_ahb_haddr                output       [31:0]
    o_ahb_hwrite               output       1
    o_ahb_hwdata               output       [31:0]
    o_ahb_htrans               output       [1:0]
    o_ahb_hsize                output       [2:0]
    o_ahb_hburst               output       [2:0]
    o_ahb_hbusreq              output       1
    i_ahb_hgrant               input        1
    i_ahb_hready               input        1
    i_ahb_hrdata               input        [31:0]
    i_ahb_hresp                input        [1:0]
    **DFI V5.0**
    ---------------------------------------------------------------  --------------------------------------------------------------------------------------------------------------
    i_dfi_clk_on               input        1                        DFI clock on request
    o_dfi_clk                  output       1
    o_dfi_ctrlupd_ack          output       1
    i_dfi_ctrlupd_req          input        1
    i_dfi_phyupd_ack           input        1
    o_dfi_phyupd_req           output       1
    o_dfi_phyupd_type          output       [1:0]
    i_dfi_freq_fsp             input        [1:0]
    i_dfi_freq_ratio           input        [1:0]
    i_dfi_frequency            input        [4:0]
    o_dfi_init_complete        output       1
    i_dfi_init_start           input        1
    i_dfi_phymstr_ack          input        1
    o_dfi_phymstr_cs_state     output       [1:0]
    o_dfi_phymstr_req          output       1
    o_dfi_phymstr_state_sel    output       1
    o_dfi_phymstr_type         output       [1:0]
    o_dfi_lp_ctrl_ack          output       1
    i_dfi_lp_ctrl_req          input        1
    i_dfi_lp_ctrl_wakeup       input        [5:0]
    o_dfi_lp_data_ack          output       1
    i_dfi_lp_data_req          input        1
    i_dfi_lp_data_wakeup       input        [5:0]
    i_dfi_reset_n_p0           input        1
    i_dfi_reset_n_p1           input        1
    i_dfi_reset_n_p2           input        1
    i_dfi_reset_n_p3           input        1
    i_dfi_address_p0           input        [13:0]
    i_dfi_address_p1           input        [13:0]
    i_dfi_address_p2           input        [13:0]
    i_dfi_address_p3           input        [13:0]
    i_dfi_cke_p0               input        [1:0]
    i_dfi_cke_p1               input        [1:0]
    i_dfi_cke_p2               input        [1:0]
    i_dfi_cke_p3               input        [1:0]
    i_dfi_cs_p0                input        [1:0]
    i_dfi_cs_p1                input        [1:0]
    i_dfi_cs_p2                input        [1:0]
    i_dfi_cs_p3                input        [1:0]
    i_dfi_dram_clk_disable_p0  input        1
    i_dfi_dram_clk_disable_p1  input        1
    i_dfi_dram_clk_disable_p2  input        1
    i_dfi_dram_clk_disable_p3  input        1
    i_dfi_wrdata_p0            input        [63:0]
    i_dfi_wrdata_p1            input        [63:0]
    i_dfi_wrdata_p2            input        [63:0]
    i_dfi_wrdata_p3            input        [63:0]
    i_dfi_parity_in_p0         input        1
    i_dfi_parity_in_p1         input        1
    i_dfi_parity_in_p2         input        1
    i_dfi_parity_in_p3         input        1
    i_dfi_wrdata_cs_p0         input        [1:0]
    i_dfi_wrdata_cs_p1         input        [1:0]
    i_dfi_wrdata_cs_p2         input        [1:0]
    i_dfi_wrdata_cs_p3         input        [1:0]
    i_dfi_wrdata_mask_p0       input        [7:0]
    i_dfi_wrdata_mask_p1       input        [7:0]
    i_dfi_wrdata_mask_p2       input        [7:0]
    i_dfi_wrdata_mask_p3       input        [7:0]
    i_dfi_wrdata_en_p0         input        1
    i_dfi_wrdata_en_p1         input        1
    i_dfi_wrdata_en_p2         input        1
    i_dfi_wrdata_en_p3         input        1
    i_dfi_wck_cs_p0            input        [1:0]
    i_dfi_wck_cs_p1            input        [1:0]
    i_dfi_wck_cs_p2            input        [1:0]
    i_dfi_wck_cs_p3            input        [1:0]
    i_dfi_wck_en_p0            input        1
    i_dfi_wck_en_p1            input        1
    i_dfi_wck_en_p2            input        1
    i_dfi_wck_en_p3            input        1
    i_dfi_wck_toggle_p0        input        [1:0]
    i_dfi_wck_toggle_p1        input        [1:0]
    i_dfi_wck_toggle_p2        input        [1:0]
    i_dfi_wck_toggle_p3        input        [1:0]
    i_dfi_rddata_cs_p0         input        [1:0]
    i_dfi_rddata_cs_p1         input        [1:0]
    i_dfi_rddata_cs_p2         input        [1:0]
    i_dfi_rddata_cs_p3         input        [1:0]
    i_dfi_rddata_en_p0         input        1
    i_dfi_rddata_en_p1         input        1
    i_dfi_rddata_en_p2         input        1
    i_dfi_rddata_en_p3         input        1
    o_dfi_rddata_dbi_w0        output       [7:0]
    o_dfi_rddata_dbi_w1        output       [7:0]
    o_dfi_rddata_dbi_w2        output       [7:0]
    o_dfi_rddata_dbi_w3        output       [7:0]
    o_dfi_rddata_w0            output       [63:0]
    o_dfi_rddata_w1            output       [63:0]
    o_dfi_rddata_w2            output       [63:0]
    o_dfi_rddata_w3            output       [63:0]
    o_dfi_rddata_valid_w0      output       1
    o_dfi_rddata_valid_w1      output       1
    o_dfi_rddata_valid_w2      output       1
    o_dfi_rddata_valid_w3      output       1
    **LPDDR4x/LPDDR5**
    ---------------------------------------------------------------  --------------------------------------------------------------------------------------------------------------
    pad_ddr_rext               inout        1                        Connect to 240 Ohm resistor
    pad_ddr_test               inout        1                        High frequency test pad
    pad_ddr_reset_n            inout        1
    pad_ch0_ddr_ca_ca0         inout        1
    pad_ch0_ddr_ca_ca1         inout        1
    pad_ch0_ddr_ca_ca2         inout        1
    pad_ch0_ddr_ca_ca3         inout        1
    pad_ch0_ddr_ca_ca4         inout        1
    pad_ch0_ddr_ca_ca5         inout        1
    pad_ch0_ddr_ca_ca6         inout        1                        LPDDR5 only
    pad_ch0_ddr_ca_cs0         inout        1
    pad_ch0_ddr_ca_cs1         inout        1
    pad_ch0_ddr_ca_cke0        inout        1                        LPDDR4x only
    pad_ch0_ddr_ca_cke1        inout        1                        LPDDR4x only
    pad_ch0_ddr_ca_ck_c        inout        1
    pad_ch0_ddr_ca_ck_t        inout        1
    pad_ch0_ddr_dq0_dbim       inout        1
    pad_ch0_ddr_dq0_dq0        inout        1
    pad_ch0_ddr_dq0_dq1        inout        1
    pad_ch0_ddr_dq0_dq2        inout        1
    pad_ch0_ddr_dq0_dq3        inout        1
    pad_ch0_ddr_dq0_dq4        inout        1
    pad_ch0_ddr_dq0_dq5        inout        1
    pad_ch0_ddr_dq0_dq6        inout        1
    pad_ch0_ddr_dq0_dq7        inout        1
    pad_ch0_ddr_dq0_wck_c      inout        1                        LPDDR5 only
    pad_ch0_ddr_dq0_wck_t      inout        1                        LPDDR5 only
    pad_ch0_ddr_dq0_dqs_c      inout        1
    pad_ch0_ddr_dq0_dqs_t      inout        1
    pad_ch0_ddr_dq1_dbim       inout        1
    pad_ch0_ddr_dq1_dq0        inout        1
    pad_ch0_ddr_dq1_dq1        inout        1
    pad_ch0_ddr_dq1_dq2        inout        1
    pad_ch0_ddr_dq1_dq3        inout        1
    pad_ch0_ddr_dq1_dq4        inout        1
    pad_ch0_ddr_dq1_dq5        inout        1
    pad_ch0_ddr_dq1_dq6        inout        1
    pad_ch0_ddr_dq1_dq7        inout        1
    pad_ch0_ddr_dq1_wck_c      inout        1                        LPDDR5 only
    pad_ch0_ddr_dq1_wck_t      inout        1                        LPDDR5 only
    pad_ch0_ddr_dq1_dqs_c      inout        1
    pad_ch0_ddr_dq1_dqs_t      inout        1
    pad_ch1_ddr_ca_ca0         inout        1
    pad_ch1_ddr_ca_ca1         inout        1
    pad_ch1_ddr_ca_ca2         inout        1
    pad_ch1_ddr_ca_ca3         inout        1
    pad_ch1_ddr_ca_ca4         inout        1
    pad_ch1_ddr_ca_ca5         inout        1
    pad_ch1_ddr_ca_ca6         inout        1                        LPDDR5 only
    pad_ch1_ddr_ca_cs0         inout        1
    pad_ch1_ddr_ca_cs1         inout        1
    pad_ch1_ddr_ca_cke0        inout        1                        LPDDR4x only
    pad_ch1_ddr_ca_cke1        inout        1                        LPDDR4x only
    pad_ch1_ddr_ca_ck_c        inout        1
    pad_ch1_ddr_ca_ck_t        inout        1
    pad_ch1_ddr_dq0_dbim       inout        1
    pad_ch1_ddr_dq0_dq0        inout        1
    pad_ch1_ddr_dq0_dq1        inout        1
    pad_ch1_ddr_dq0_dq2        inout        1
    pad_ch1_ddr_dq0_dq3        inout        1
    pad_ch1_ddr_dq0_dq4        inout        1
    pad_ch1_ddr_dq0_dq5        inout        1
    pad_ch1_ddr_dq0_dq6        inout        1
    pad_ch1_ddr_dq0_dq7        inout        1
    pad_ch1_ddr_dq0_wck_c      inout        1                        LPDDR5 only
    pad_ch1_ddr_dq0_wck_t      inout        1                        LPDDR5 only
    pad_ch1_ddr_dq0_dqs_c      inout        1
    pad_ch1_ddr_dq0_dqs_t      inout        1
    pad_ch1_ddr_dq1_dbim       inout        1
    pad_ch1_ddr_dq1_dq0        inout        1
    pad_ch1_ddr_dq1_dq1        inout        1
    pad_ch1_ddr_dq1_dq2        inout        1
    pad_ch1_ddr_dq1_dq3        inout        1
    pad_ch1_ddr_dq1_dq4        inout        1
    pad_ch1_ddr_dq1_dq5        inout        1
    pad_ch1_ddr_dq1_dq6        inout        1
    pad_ch1_ddr_dq1_dq7        inout        1
    pad_ch1_ddr_dq1_wck_c      inout        1                        LPDDR5 only
    pad_ch1_ddr_dq1_wck_t      inout        1                        LPDDR5 only
    pad_ch1_ddr_dq1_dqs_c      inout        1
    pad_ch1_ddr_dq1_dqs_t      inout        1
    ========================== ===========  =======================  ==============================================================================================================

Interfaces
----------

AHB-Lite Slave Interface
++++++++++++++++++++++++

The AHB slave interface is used for configuration and status register access. The AHB slave interface does not support HPROT or HMASTLOCK signals.

AHB-Lite Master Interface
+++++++++++++++++++++++++

The DDR PHY's AHB master interface enables the embedded RISC-V MicroController Unit (MCU) to control PHY-external logic, such as, Memory Controller interfaces and CSRs, sensors, etc. The AHB master interface does not support HPROT or HMASTLOCK signals.

DFIv5.0 Interface
+++++++++++++++++

The DFIv5.0 compliant interface provides connectivity to a compatible Memory Controller. The DDR PHY uses an embedded PLL to generate a low jitter DRAM clock and provides a DFI clock to the Memory Controller.

The DDR PHY supports the following DFI features.

   * 1:2 and 1:4 frequency ratios

The DDR PHY currently does not support the following DFI features.

   * Error interface
   * Message interface
   * ODT signal

LPDDR4x Interface
+++++++++++++++++

The LPDDR4x compliant interface supports up to two 1x16 channels and two ranks. The DDR PHY does not support the ODT output pin. DRAM termination shall be set through MRW.

LPDDR5 Interface
++++++++++++++++

The LPDDR5 compliant interface supports up to two 1x16 channels and two ranks. The DDR PHY does not support the ODT output pin. DRAM termination shall be set through MRW.

Technology
----------

The Wavious DDR PHY has been initially developed in the GF12LPP process. Although the DDR PHY is highly digital in nature (e.g. no bandgaps) to improve portability to various foundries and process nodes, the DRAM protocol high transfer rates and varying channel characteristics require high performance mixed-signal and analog PHY circuits. The Wavious DDR PHY design includes various wrappers to ease standard cell migration and analog models for simulations. To port the DDR PHY to other process nodes, designers must perform two tasks. Firstly, designers must incorporate process-specific standard cells into the technology wrappers. Secondly, designers must create analog and mixed-signal schematics/layout which implement high performance circuits. The sections below describe the specific wrappers and models that can be leveraged to support DDR PHY process technology porting.

.. note ::
  * Datasheets for mixed-signal and analog circuits will be included in future releases.

rtl/tech
++++++++

This directory includes standard cell wrappers. The DDR PHY design uses these wrappers exclusively to maximize code reuse. Designers should map technology specific cells into these wrappers.

* **ddr_custom_lib.sv**   - DDR cells for high performance datapath
* **ddr_stdcell_lib.sv**  - DDR cells for physical design (may be the same as wav_stdcell_lib cells depending on performance requirements)
* **wav_stdcell_lib.sv**  - General cells for physical design
* **wav_tcm_sp.sv**       - Single port SRAM for tightly coupled memory

rtl/custom_ip
+++++++++++++

This directory includes high performance mixed-signal circuit models that are used in various contexts within the DDR PHY. Designers must create process-specific mixed-signal schematics/layout for these circuits.

* **wphy_2to1_14g_rvt.sv**                 - Differential 2:1 serializer
* **wphy_cgc_diff_lvt.sv**                 - Differential clock gating cell (rest low)
* **wphy_cgc_diff_svt.sv**                 - Differential clock gating cell (rest low)
* **wphy_cgc_diff_rh_lvt.sv**              - Differential clock gating cell (rest high)
* **wphy_cgc_diff_rh_svt.sv**              - Differential clock gating cell (rest high)
* **wphy_clk_div_2ph_4g_dlymatch_lvt.sv**  - 2 phase clock divider delay match
* **wphy_clk_div_2ph_4g_dlymatch_svt.sv**  - 2 phase clock divider delay match
* **wphy_clk_div_2ph_4g_lvt.sv**           - 2 phase clock divider
* **wphy_clk_div_2ph_4g_svt.sv**           - 2 phase clock divider
* **wphy_clk_div_4ph_10g_dlymatch_svt.sv** - 4 phase clock divider delay match
* **wphy_clk_div_4ph_10g_svt.sv**          - 4 phase clock divider
* **wphy_clkmux_3to1_diff.sv**             - Differential 3:1 clock mux
* **wphy_clkmux_3to1_diff_slvt.sv**        - Differential 3:1 clock mux (low latency)
* **wphy_clkmux_diff.sv**                  - Differential 2:1 clock mux
* **wphy_gfcm_lvt.sv**                     - Glitch free clock mux
* **wphy_gfcm_svt.sv**                     - Glitch free clock mux
* **wphy_pi_4g.sv**                        - Phase interpolator
* **wphy_pi_dly_match_4g.sv**              - Phase interpolator delay match
* **wphy_prog_dly_se_4g.sv**               - Programmable delay
* **wphy_prog_dly_se_4g_small.sv**         - Programmable delay (low latency)
* **wphy_sa_4g_2ph_pdly_no_esd.sv**        - Sense amplifier without ESD

rtl/ddr_ip
++++++++++

This directory includes DDR PHY specific analog and mixed-signal components including IO pad models. Designers must create process-specific analog and mixed-signal schematics/layout for these circuits.

* **wphy_lp4x5_cmn.sv**                    - Common clock
* **wphy_lp4x5_cmn_clks_svt.sv**           - Common clock driver
* **wphy_lp4x5_cke_drvr_w_lpbk.sv**        - CKE pad driver
* **wphy_lp4x5_dq_drvr_w_lpbk.sv**         - DQ pad driver with loopback and ESD
* **wphy_lp4x5_dqs_drvr_w_lpbk.sv**        - DQS pad driver with loopback and ESD
* **wphy_lp4x5_dqs_rcvr_no_esd.sv**        - DQS pad receiver without ESD

rtl/mvppll_ip
+++++++++++++

This directory includes the multi-VCO PLL analog model. Designers must create process-specific analog and mixed-signal schematics/layout for these circuits.

* **wphy_rpll_mvp_4g.sv**                  - Multi-VCO PLL

rtl/wddr
++++++++

This directory includes the DDR PHY foundation digital control and datapath circuits. All blocks within this directory can be synthesized to a target technology assuming that standard cell wrappers have been updated appropriately. The Wavious DDR PHY is highly configurable and uses a common slice-based design methodology that is leveraged for DQ, DQS, CA, CK, CS, CKE, DBI, DM, etc. functional slices. Depending on design constraints (schedules, area, power, performance, etc), designers can implement the DDR PHY datapath in a physical design flow or a custom layout flow. The implementation methodology will have implications for tool flows, timing closure, signoff, etc. that should be carefully considered.
