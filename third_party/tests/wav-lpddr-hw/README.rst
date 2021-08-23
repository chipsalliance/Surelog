https://github.com/waviousllc/wav-lpddr-hw

.. figure :: docs/source/wavious_logo.png
  :align:    center

WDDR PHY
========
The Wavious DDR (WDDR) Physical interface (PHY) is designed to be a scalable DDR PHY IP that meets high performance, low area, and low power
requirements across multiple JEDEC DRAM protocols. Initially targeting LPDDR4x and LPDDR5, the WDDR PHY supports JEDEC LPDDR protocols and a DFIv5
compliant interface.

Features
++++++++
* LPDDR4x @4266 Mbps
* LPDDR5 @6400 Mbps
* Dual rank support
* DFI5.0 compliant Memory Controller interface
* Integrated MicroController Unit (MCU) with embedded SRAM
* Embedded training buffer
* Embedded calibration logic
* Embedded high-performance and low jitter PLL
* Per-bit deskew

Software
++++++++
The Software for Wavious DDR is located here:
https://github.com/waviousllc/wav-lpddr-sw. Software binaries are compiled and converted to ramfiles, located at ./sw directory.

Tools Required
--------------
The WDDR UVM testbench has been developed with Cadence VIP and simulators. Users must ensure that the VIP and tools have been installed properly.

Simulations without VIP
-----------------------
The testbench can be run without VIP models for the Memory Controller and LPDDR DRAM to test basic functionality. Two tests have been provided.

* MCU boot test @422Mhz.
* Sanity ddr loopback test @2112Mhz.

Run your first sims
-------------------
Ensure that Cadence Xcelium simulator (v20.09.003) is installed. Update verif/run/simulate.sh variables as needed.

::

  cd verif/run
  ./simulate.sh -t wddr_dt_mcuboot_test -sw "RAMFILE_DIR_WDDR_BOOT"
  ./simulate.sh -t wddr_dt_ddr_test -e "+MVP_FORCE_PLL +vcoFreq1=2112 +gb=2 +freqRatio=2" -timeout 10000000
